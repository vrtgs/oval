use crate::compile::interner;
use crate::compile::interner::Interner;
use crate::compile::syntax::sealed::SealedParseAst;
use crate::compile::syntax::{OvalParserExt, ParserExtra};
use crate::compile::tokenizer::Token;
use crate::symbol::path_inner::{FromFile, PathInner, ResolvableIdent};
use alloc::string::String;
use alloc::vec::Vec;
use chumsky::input::{Input, MapExtra};
use chumsky::span::SimpleSpan;
use chumsky::{IterParser, Parser};
use core::fmt::{Debug, Formatter};
use core::hash::Hash;
pub use interner::Symbol;
use string_interner::Symbol as _;

#[derive(Copy, Clone)]
#[repr(align(2))]
// ensure this matches the same layout header of Path
pub struct Ident {
    symbol: Symbol,
}

mod path_inner;

impl SealedParseAst for Ident {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        use chumsky::primitive;

        primitive::just(Token::Ident)
            .map_with(|_, extra: &mut MapExtra<'a, '_, I, ParserExtra<'a>>| {
                let span: SimpleSpan = extra.span();
                let (source, compiler) = &mut extra.state().0;
                let str = &source.contents()[span.into_range()];
                let symbol = compiler.intern(str);
                Ident { symbol }
            })
            .labelled("identifier")
    }
}

#[derive(Clone)]
pub struct Path(PathInner);

// inner
impl Path {
    pub fn is_root(&self) -> bool {
        self.0.is_root()
    }

    pub fn make_root(self, interner: &mut Interner) -> Self {
        Self(self.0.make_root(interner))
    }

    pub fn make_relative(self, interner: &mut Interner) -> Self {
        Self(self.0.make_relative(interner))
    }

    pub fn idents(&self) -> &[Ident] {
        self.0.idents()
    }

    pub fn first(&self) -> Ident {
        self.0.first()
    }

    pub fn last(&self) -> Ident {
        self.0.last()
    }

    pub fn split_first(&self) -> (Ident, &[Ident]) {
        self.0.split_first()
    }
    pub fn split_last(&self) -> (&[Ident], Ident) {
        self.0.split_last()
    }
}

impl Path {
    pub(crate) fn invalid() -> Self {
        Self(PathInner::construct_inline(Ident {
            symbol: Symbol::try_from_usize(0).unwrap(),
        }))
    }

    fn from_idents_inner<I: ResolvableIdent>(
        root: bool,
        idents: &[I],
        interner: &mut Interner,
        ext: &I::Extra<'_>,
    ) -> Path {
        let [first, rest @ ..] = idents else {
            panic!("Paths require at least 1 Ident to construct")
        };

        // hot path; no alloc
        if !root && rest.is_empty() {
            return Path(PathInner::construct_inline(first.value()));
        }

        let first_hint = first.len(interner, ext);

        let size_hint = first_hint.map_or(0, |first| {
            let rest_iter = rest
                .iter()
                .map(|ident| ident.len(interner, ext));

            rest_iter
                .map(|opt| {
                    opt.expect("a resolvable ident type, either always returns Some, or always returns None")
                })
                .fold(first, |last_ident_len, ident_len| last_ident_len + 2 + ident_len)
        });

        let size_hint = size_hint + (root as usize * 2);

        let mut symbol = String::with_capacity(size_hint);

        let resolve = |ident: &I| ident.resolve(interner, ext);
        let builder_slice = match root {
            true => idents,
            false => {
                symbol += resolve(first);
                rest
            }
        };

        for ident in builder_slice {
            symbol += "::";
            symbol += resolve(ident)
        }

        Path(PathInner::construct_alloc(
            root,
            interner.intern(&symbol),
            idents,
        ))
    }

    pub fn from_idents(root: bool, idents: &[Ident], interner: &mut Interner) -> Path {
        Self::from_idents_inner(root, idents, interner, &())
    }
}

impl SealedParseAst for Path {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        use chumsky::primitive::just;

        just(Token::DoubleColon)
            .or_not()
            .map(|opt| opt.is_some())
            .then(
                Ident::parser()
                    .spanned()
                    .map(FromFile)
                    .separated_by(just(Token::DoubleColon))
                    .at_least(1)
                    .collect::<Vec<_>>(),
            )
            .map_with(|(root, idents), extra| {
                let (source, compiler) = &mut extra.state().0;
                Self::from_idents_inner(root, &idents, compiler, source)
            })
    }
}

mod sealed {
    use crate::compile::interner;

    pub trait Sealed {
        fn symbol(&self) -> interner::Symbol;
    }

    impl<S: Sealed> Sealed for &S {
        fn symbol(&self) -> interner::Symbol {
            <S as Sealed>::symbol(*self)
        }
    }
}

pub trait SymbolLike: sealed::Sealed {}

impl sealed::Sealed for Symbol {
    fn symbol(&self) -> Symbol {
        *self
    }
}

impl<S: sealed::Sealed> SymbolLike for S {}

macro_rules! symbol_based {
    ($($ty:ty => $(@$prefix: tt. )* $symbol:ident $(($($args:tt)*))?),+ $(,)?) => {
        $(
        impl PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                self $(.$prefix)* .$symbol $(($($args)*))? == other$(.$prefix)* .$symbol $(($($args)*))?
            }
        }

        impl Eq for $ty {}

        impl Hash for $ty {
            fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
                Hash::hash(&self$(.$prefix)*.$symbol$(($($args)*))?, state)
            }
        }

        impl sealed::Sealed for $ty {
            fn symbol(&self) -> interner::Symbol {
                sealed::Sealed::symbol(&self$(.$prefix)*.$symbol$(($($args)*))?)
            }
        }

        impl Debug for $ty {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($ty)).finish_non_exhaustive()
            }
        }
        )+
    };
}

symbol_based!(
    Ident => symbol,
    Path => @0.symbol(),
);

// this should always be cheap, this is a very hot path
impl PartialEq<Ident> for Path {
    fn eq(&self, other: &Ident) -> bool {
        self.0.symbol() == other.symbol
    }
}
