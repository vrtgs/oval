use crate::parser::{AstParse, InputTape, OvalParser, ParserData};
use crate::tokens::TokenTy;
use crate::tokens::{Comma, CurlyBrace, Paren, SquareBracket, TokenKind};
use alloc::vec::Vec;
use chumsky::IterParser;
use chumsky::Parser;
use chumsky::input::InputRef;
use chumsky::prelude::just;
use core::marker::PhantomData;
use chumsky::recovery::ViaParser;
use crate::ast::recursive::Recursive;
use crate::recurse;
use crate::spanned::{Span, Spanned};

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

// #[derive(Copy, Clone)]
// pub(crate) struct WrapBox<F>(F);
//
// impl<I, O, F: TupleCall<Box<I>, O>> TupleCall<I, O> for WrapBox<F> {
//     fn call(&self, args: I) -> O {
//         let args = Box::new(args);
//         self.0.call(args)
//     }
// }

#[derive(Copy, Clone)]
pub(crate) struct WrapRecursive<F>(F);

impl<I, O, F: TupleCall<Recursive<I>, O>> TupleCall<I, O> for WrapRecursive<F> {
    fn call(&self, args: I) -> O {
        let args = Recursive::new(args);
        self.0.call(args)
    }
}

impl<'src, P, O, F1, F2, I, T, E: ParserData<'src, I>>
    chumsky::extension::v1::ExtParser<'src, I, T, E> for TupleParserInner<P, O, F1, F2, T>
where
    I: InputTape<'src>,
    P: OvalParser<'src, I, O, E>,
    F1: TupleCall<TokenTy!['(', O, ')'], T>,
    F2: TupleCall<TokenTy!['(', Vec<O>, ')'], T>,
{
    fn parse(&self, inp: &mut InputRef<'src, '_, I, E>) -> Result<T, E::Error> {
        inp.parse(
            (&self.parser)
                .separated_by(Comma::parser())
                .collect::<Vec<_>>()
                .then(Comma::parser().or_not())
                .in_parens(),
        )
        .map(move |parens| {
            let span = parens.span();

            let Paren {
                0: (mut list, leading),
                ..
            } = parens;

            if leading.is_none() {
                match <[O; 1]>::try_from(list) {
                    Ok([x]) => return self.parens.call(Paren::new(x, span)),
                    Err(fail) => list = fail,
                }
            }

            self.tuple.call(Paren::new(list, span))
        })
    }

    fn check(&self, inp: &mut InputRef<'src, '_, I, E>) -> Result<(), E::Error> {
        inp.check(
            (&self.parser)
                .separated_by(Comma::parser())
                .allow_trailing()
                .in_parens(),
        )
    }
}

pub(crate) type TupleParser<P, O, F1, F2, T> =
    chumsky::extension::v1::Ext<TupleParserInner<P, O, F1, F2, T>>;

macro_rules! impl_delimiters {
    ($self: expr, $delimiter: ident) => {{
        paste::paste! {
            $self
                .delimited_by(
                    static_parser! { just(TokenKind::[<L $delimiter>]) },
                    static_parser! { just(TokenKind::[<R $delimiter>]) },
                )
                .map_with(|out, extra| {
                    let span = extra.span();
                    $delimiter::new(out, span)
                })
        }
    }};
}

pub(crate) trait OvalParserExt<'src, I: InputTape<'src>, O, E: ParserData<'src, I>>:
    OvalParser<'src, I, O, E> + Sized
{
    fn in_parens(self) -> impl OvalParser<'src, I, TokenTy!['(', O, ')'], E> {
        impl_delimiters!(self, Paren)
    }

    fn recursive_tuple<T, F1, F2>(
        self,
        parens: F1,
        tuple: F2,
    ) -> TupleParser<Self, O, WrapRecursive<F1>, WrapRecursive<F2>, T>
    where
        F1: FnOnce(Recursive<TokenTy!['(', O, ')']>) -> T + Copy,
        F2: FnOnce(Recursive<TokenTy!['(', Vec<O>, ')']>) -> T + Copy,
        Self: Copy,
    {
        chumsky::extension::v1::Ext(TupleParserInner {
            parser: self,
            parens: WrapRecursive(parens),
            tuple: WrapRecursive(tuple),
            _output_parser: PhantomData,
        })
    }

    fn in_square_brackets(self) -> impl OvalParser<'src, I, TokenTy!['[', O, ']'], E> {
        impl_delimiters!(self, SquareBracket)
    }

    fn in_curly_brackets(self) -> impl OvalParser<'src, I, TokenTy!['{', O, '}'], E> {
        impl_delimiters!(self, CurlyBrace)
    }
}

impl<'src, I: InputTape<'src>, O, E: ParserData<'src, I>, P: OvalParser<'src, I, O, E>>
    OvalParserExt<'src, I, O, E> for P
{
}

#[inline(always)]
pub(crate) const fn recursive_parser<'src, T: AstParse, I: InputTape<'src>, E: ParserData<'src, I>>()
-> impl OvalParser<'src, I, T, E> {
    const {
        chumsky::primitive::custom(|input| {
            recurse(move || input.parse(T::parser()))
        })
    }
}

pub(crate) const fn static_parser_inner<'src, F, O, P, I: InputTape<'src>, E: ParserData<'src, I>>(
    func: F
) -> impl OvalParser<'src, I, O, E>
    where
        F: Fn() -> P + Copy + Send + Sync + 'static,
        P: Parser<'src, I, O, E>
{
    chumsky::primitive::custom(move |input| {
        input.parse(func())
    })
}

macro_rules! static_parser {
    ($($body: tt)*) => {
        // prevent an explosion in symbols that rust generates
        // if we don't unsize we get linker errors if the symbols are not stripped
        // and compile times go to the moon
        $crate::parser::static_unsized_parser! {
            $($body)*
        }
    };
}

macro_rules! static_unsized_parser {
    ($($body: tt)*) => {
        const {
            $crate::parser::static_parser_inner(move || {
                let parser = &const { crate::parser::static_parser_inner(move || { $($body)* }) };
                // store the parser in static memory
                // this parser is OvalParser - the copy requirement
                // well after being referenced it gains it again, and we get the OvalParser back
                let parser: &(dyn ::chumsky::Parser<_, _, _> + Send + Sync) = parser;
                parser
            })
        }
    };
}

pub(crate) use {static_unsized_parser, static_parser};

struct DelimitedTokens;

impl AstParse for DelimitedTokens {
    fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>() -> impl OvalParser<'src, I, Self, E> {
        static_parser! {
            const DELIMITERS: [[TokenKind; 2]; 3] = [
                [TokenKind::LParen, TokenKind::RParen],
                [TokenKind::LSquareBracket, TokenKind::RSquareBracket],
                [TokenKind::LCurlyBrace, TokenKind::RCurlyBrace],
            ];

            let parse_single = chumsky::primitive::choice((
                chumsky::primitive::none_of(DELIMITERS.as_flattened()).ignored(),
                recursive_parser::<Self, I, E>().in_parens().ignored(),
                recursive_parser::<Self, I, E>().in_square_brackets().ignored(),
                recursive_parser::<Self, I, E>().in_curly_brackets().ignored(),
            ));

            parse_single.repeated().map(|()| DelimitedTokens)
        }
    }
}


pub trait Delimiter<T: Sized>: Sized {
    fn in_self<'src, I: InputTape<'src>, E: ParserData<'src, I>>(
        parser: impl OvalParser<'src, I, T, E>
    ) -> impl OvalParser<'src, I, Self, E>;
}

macro_rules! impl_delimiters {
    ($($method: ident = $l_paren: tt $r_paren: tt)+) => {

$(impl<T> Delimiter<T> for TokenTy![$l_paren, T, $r_paren] {
    fn in_self<'src, I: InputTape<'src>, E: ParserData<'src, I>>(parser: impl OvalParser<'src, I, T, E>)
        -> impl OvalParser<'src, I, Self, E>
    {
        parser.$method()
    }
})+
    };
}


impl_delimiters! {
    in_parens = '(' ')'
    in_square_brackets = '[' ']'
    in_curly_brackets = '{' '}'
}

pub(crate) fn recover_nested_delimiters_extra<'src, D: Delimiter<T>, T, I: InputTape<'src>, E: ParserData<'src, I>>(
    fallback: impl Fn(Span) -> T + Copy + Send + Sync + 'static
) -> impl OvalParser<'src, I, D, E> {
    let inner = DelimitedTokens::parser()
        .map_with(move |_, extra| {
            fallback(extra.span())
        });

    D::in_self(inner)
}

pub(crate) fn recover_nested_delimiters<'src, D: Delimiter<T>, T: Default, I: InputTape<'src>, E: ParserData<'src, I>>(
) -> ViaParser<impl OvalParser<'src, I, D, E>> {
    chumsky::recovery::via_parser(recover_nested_delimiters_extra(
        |_| T::default()
    ))
}
