use crate::compile::Spanned;
use crate::compile::error::Error;
use crate::compile::interner::Interner;
use crate::compile::source::{Source, SourceId};
use crate::compile::syntax::item::Item;
use crate::compile::syntax::sealed::SealedParseAst;
use crate::compile::tokenizer::{Token, TokenizedSource, tokenize};
use crate::symbol::{Ident, Path};
use alloc::boxed::Box;
use alloc::vec::Vec;
use chumsky::combinator::{DelimitedBy, MapWith};
use chumsky::error::Rich;
use chumsky::extra::SimpleState;
use chumsky::input::{Input, InputRef, MapExtra};
use chumsky::prelude::just;
use chumsky::primitive::Just;
use chumsky::span::SimpleSpan;
use chumsky::util::IntoMaybe;
use chumsky::{IterParser, Parser};
use std::marker::PhantomData;

pub mod block;
pub mod item;
pub mod r#type;

pub(crate) type ParserExtra<'a> = chumsky::extra::Full<
    Rich<'a, Token, SimpleSpan>,
    SimpleState<(&'a Source<'a>, &'a mut Interner)>,
    (),
>;

pub(crate) type Delimited<'a, T, I> =
    DelimitedBy<T, Just<Token, I, ParserExtra<'a>>, Just<Token, I, ParserExtra<'a>>, Token, Token>;

pub(crate) struct TupleParserInner<P, O, F1, F2, T> {
    parser: P,
    parens: F1,
    tuple: F2,
    _output_parser: PhantomData<fn(O) -> T>,
}

impl<P: Clone, O, F1: Clone, F2: Clone, T> Clone for TupleParserInner<P, O, F1, F2, T> {
    fn clone(&self) -> Self {
        Self {
            parser: self.parser.clone(),
            parens: self.parens.clone(),
            tuple: self.tuple.clone(),
            _output_parser: PhantomData,
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.parser.clone_from(&source.parser);
        self.parens.clone_from(&source.parens);
        self.tuple.clone_from(&source.tuple);
    }
}

impl<P: Copy, O, F1: Copy, F2: Copy, T> Copy for TupleParserInner<P, O, F1, F2, T> {}

trait TupleCall<I, O> {
    fn call(&self, args: I) -> O;
}

impl<I, O, F: Fn(I) -> O> TupleCall<I, O> for F {
    fn call(&self, args: I) -> O {
        self(args)
    }
}

#[derive(Copy, Clone)]
pub(crate) struct BoxFirst<F>(F);

impl<I, O, F: TupleCall<Box<I>, O>> TupleCall<I, O> for BoxFirst<F> {
    fn call(&self, args: I) -> O {
        let args = Box::new(args);
        self.0.call(args)
    }
}

impl<'a, P, O, F1, F2, I, T> chumsky::extension::v1::ExtParser<'a, I, T, ParserExtra<'a>>
    for TupleParserInner<P, O, F1, F2, T>
where
    I: Input<'a, Token = Token, Span = SimpleSpan>,
    P: Parser<'a, I, O, ParserExtra<'a>>,
    F1: TupleCall<O, T>,
    F2: TupleCall<Vec<O>, T>,
{
    fn parse(
        &self,
        inp: &mut InputRef<'a, '_, I, ParserExtra<'a>>,
    ) -> Result<T, <ParserExtra<'a> as chumsky::extra::ParserExtra<'a, I>>::Error> {
        inp.parse(
            (&self.parser)
                .separated_by(just(Token::Comma))
                .collect::<Vec<_>>()
                .then(just(Token::Comma).or_not())
                .in_parens(),
        )
        .map(move |(mut list, leading)| {
            if leading.is_none() {
                match <[O; 1]>::try_from(list) {
                    Ok([x]) => return self.parens.call(x),
                    Err(fail) => list = fail,
                }
            }

            self.tuple.call(list)
        })
    }

    fn check(
        &self,
        inp: &mut InputRef<'a, '_, I, ParserExtra<'a>>,
    ) -> Result<(), <ParserExtra<'a> as chumsky::extra::ParserExtra<'a, I>>::Error> {
        inp.check(
            (&self.parser)
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .in_parens(),
        )
    }
}

pub(crate) type TupleParser<P, O, F1, F2, T> =
    chumsky::extension::v1::Ext<TupleParserInner<P, O, F1, F2, T>>;

pub(crate) trait OvalParserExt<'a, I: Input<'a, Token = Token, Span = SimpleSpan>, O>:
    Parser<'a, I, O, ParserExtra<'a>> + Sized
{
    fn in_parens(self) -> Delimited<'a, Self, I> {
        self.delimited_by(just(Token::LParen), just(Token::RParen))
    }

    fn box_or_tuple<T, F1, F2>(
        self,
        parens: F1,
        tuple: F2,
    ) -> TupleParser<Self, O, BoxFirst<F1>, F2, T>
    where
        F1: Fn(Box<O>) -> T + Copy,
        F2: Fn(Vec<O>) -> T + Copy,
        Self: Copy,
    {
        chumsky::extension::v1::Ext(TupleParserInner {
            parser: self,
            parens: BoxFirst(parens),
            tuple,
            _output_parser: PhantomData,
        })
    }

    fn in_square_brackets(self) -> Delimited<'a, Self, I> {
        self.delimited_by(just(Token::LSquareBracket), just(Token::RSquareBracket))
    }

    fn in_curly_brackets(self) -> Delimited<'a, Self, I> {
        self.delimited_by(just(Token::LBracket), just(Token::RBracket))
    }

    fn spanned(
        self,
    ) -> MapWith<
        Self,
        O,
        impl Fn(O, &mut MapExtra<'a, '_, I, ParserExtra<'a>>) -> Spanned<O> + Copy + Send + Sync,
    > {
        self.map_with(|value, extra| Spanned {
            span: extra.span(),
            value,
        })
    }
}

impl<
    'a,
    I: Input<'a, Token = Token, Span = SimpleSpan>,
    O,
    P: Parser<'a, I, O, ParserExtra<'a>> + Sized,
> OvalParserExt<'a, I, O> for P
{
}

pub(crate) mod sealed {
    use crate::compile::Spanned;
    use crate::compile::syntax::{OvalParserExt, ParserExtra};
    use crate::compile::tokenizer::Token;
    use chumsky::Parser;
    use chumsky::input::Input;
    use chumsky::prelude::SimpleSpan;

    pub trait SealedParseAst: Sized + 'static {
        fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
        -> impl Parser<'a, I, Self, ParserExtra<'a>> + Copy;
    }

    impl<T: SealedParseAst> SealedParseAst for Spanned<T> {
        fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
        -> impl Parser<'a, I, Self, ParserExtra<'a>> + Copy {
            T::parser().spanned()
        }
    }
}

pub trait ParseAst: SealedParseAst {}

impl<S: SealedParseAst> ParseAst for S {}

#[derive(Debug, Clone)]
pub enum Pattern {
    Ident(Ident),
    Wildcard,
}

impl SealedParseAst for Pattern {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Copy {
        Ident::parser()
            .map(Pattern::Ident)
            .or(just(Token::Wildcard).map(|_| Pattern::Wildcard))
    }
}

fn recursive_parser<'a, O: ParseAst, I: Input<'a, Token = Token, Span = SimpleSpan>>()
-> impl Parser<'a, I, O, ParserExtra<'a>> + Copy + Send + Sync + 'a {
    chumsky::primitive::custom(|inp| {
        let func = move || inp.parse(O::parser());
        cfg_if::cfg_if! {
            if #[cfg(feature = "stacker")] {
                // at least 128 kib
                // and if not available grow by 2 mib
                stacker::maybe_grow(128 * 1024, 2024 * 1024, func)
            } else {
                func()
            }
        }
    })
}

fn parse_inner<'a: 'src, 'src, I: Input<'src, Token = Spanned<Token>>, O: ParseAst>(
    source: &'src Source<'a>,
    input: I,
    convert: impl Fn(
        I::MaybeToken,
    ) -> (
        <I::MaybeToken as IntoMaybe<'src, I::Token>>::Proj<Token>,
        <I::MaybeToken as IntoMaybe<'src, I::Token>>::Proj<SimpleSpan>,
    ) + 'src,
    interner: &'src mut Interner,
) -> Result<O, Error<'a>> {
    let contents = source.contents();
    let tokens = Input::map(input, (contents.len()..contents.len()).into(), convert);

    let mut state: SimpleState<(&Source, &mut Interner)> = SimpleState((source, interner));

    O::parser()
        .parse_with_state(tokens, &mut state)
        .into_result()
        .map_err(move |errors| Error::syntax_error(source.clone(), errors))
}

pub(crate) fn parse_str<O: ParseAst>(source: &str, interner: &mut Interner) -> Option<O> {
    let source = Source::new(SourceId(0), Path::invalid(), source);

    let input = chumsky::input::IterInput::new(
        tokenize(source.contents()).map_while(|maybe_token| {
            let token = Spanned::<Token> {
                span: maybe_token.span,
                value: maybe_token.value.ok()?,
            };

            Some((token, 0..0))
        }),
        0..0,
    );
    let res = parse_inner(&source, input, |value| (value.value, value.span), interner);

    res.ok()
}

pub fn parse<'a, O: ParseAst>(
    tokenized: &TokenizedSource<'a>,
    interner: &mut Interner,
) -> Result<O, Error<'a>> {
    parse_inner(
        tokenized.source(),
        tokenized.tokens_slice(),
        |spanned: &Spanned<Token>| (&spanned.value, &spanned.span),
        interner,
    )
}

#[derive(Debug)]
pub struct OvalFile<'a> {
    pub source: Source<'a>,
    pub items: Vec<Spanned<Item>>,
}

pub fn parse_file<'a>(
    tokenized: TokenizedSource<'a>,
    compiler: &mut Interner,
) -> Result<OvalFile<'a>, Error<'a>> {
    struct Items(Vec<Spanned<Item>>);

    impl SealedParseAst for Items {
        fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
        -> impl Parser<'a, I, Self, ParserExtra<'a>> + Copy {
            Item::parser().spanned().repeated().collect().map(Items)
        }
    }

    let source = tokenized.source();
    parse::<Items>(&tokenized, compiler).map(|items| OvalFile {
        source: source.clone(),
        items: items.0,
    })
}
