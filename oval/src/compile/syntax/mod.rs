use crate::compile::Spanned;
use crate::compile::error::Error;
use crate::compile::interner::Interner;
use crate::compile::source::{Source, SourceId};
use crate::compile::syntax::item::Item;
use crate::compile::syntax::sealed::SealedParseAst;
use crate::compile::tokenizer::{Token, TokenizedSource, tokenize};
use crate::symbol::{Ident, Path};
use alloc::vec::Vec;
use chumsky::combinator::{DelimitedBy, MapWith};
use chumsky::error::Rich;
use chumsky::extra::SimpleState;
use chumsky::input::{Input, MapExtra};
use chumsky::prelude::just;
use chumsky::primitive::Just;
use chumsky::span::SimpleSpan;
use chumsky::util::IntoMaybe;
use chumsky::{IterParser, Parser};

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

pub(crate) trait OvalParserExt<'a, I: Input<'a, Token = Token, Span = SimpleSpan>, O>:
    Parser<'a, I, O, ParserExtra<'a>> + Sized
{
    fn in_parens(self) -> Delimited<'a, Self, I> {
        self.delimited_by(just(Token::LParen), just(Token::RParen))
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
        -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone;
    }

    impl<T: SealedParseAst> SealedParseAst for Spanned<T> {
        fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
        -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
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
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
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
    pub items: Vec<Item>,
}

pub fn parse_file<'a>(
    tokenized: TokenizedSource<'a>,
    compiler: &mut Interner,
) -> Result<OvalFile<'a>, Error<'a>> {
    struct Items(Vec<Item>);

    impl SealedParseAst for Items {
        fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
        -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
            Item::parser().repeated().collect().map(Items)
        }
    }

    let source = tokenized.source();
    parse::<Items>(&tokenized, compiler).map(|items| OvalFile {
        source: source.clone(),
        items: items.0,
    })
}
