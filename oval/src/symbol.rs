use string_interner::Symbol as _;
use core::hash::Hash;
use alloc::vec::Vec;
use alloc::string::String;
use chumsky::input::{MapExtra, ValueInput};
use chumsky::{IterParser, Parser};
use chumsky::span::SimpleSpan;
use crate::compile::{interner, Spanned};
use crate::compile::parser::{OvalParserExt, ParserExtra};
use crate::compile::parser::sealed::SealedParseAst;
use crate::compile::tokenizer::Token;


#[derive(Copy, Clone, Debug)]
pub struct Ident {
    symbol: interner::Symbol
}

impl SealedParseAst for Ident {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        use chumsky::primitive;

        primitive::just(Token::Ident)
            .map_with(|_, extra: &mut MapExtra<'a, '_, I, ParserExtra<'a>>| {
                let span: SimpleSpan = extra.span();
                let (source, compiler) = &mut extra.state().0;
                let str = &source.contents()[span.into_range()];
                let symbol = compiler.intern(str);
                Ident {
                    symbol,
                }
            })
            .labelled("identifier")

    }
}

#[derive(Clone, Debug)]
pub struct Path {
    symbol: interner::Symbol,
    // idents: MinSizedCowArray<Ident, 1>
}

impl Path {
    pub(crate) fn invalid() -> Self {
        Path {
            symbol: interner::Symbol::try_from_usize(0).unwrap(),
        }
    }
}

impl SealedParseAst for Path {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        use chumsky::primitive::just;

        just(Token::DoubleColon).or_not().map(|opt| opt.is_some())
            .then(Ident::parser().spanned().separated_by(just(Token::DoubleColon))
            .at_least(1)
            .collect::<Vec<_>>()
        ).map_with(|(root, mut idents), extra| {
            let (source, compiler) = &mut extra.state().0;

            debug_assert!(!idents.is_empty());

            if root {
                let root_ident = Spanned {
                    // the span being 0..0 is crucial for logic
                    // check comment bellow
                    span: SimpleSpan::from(0..0),
                    value: Ident {
                        symbol: compiler.intern("{{root}}")
                    }
                };

                idents.insert(0, root_ident)
            }

            if let [ident] = &*idents {
                return Path {
                    symbol: ident.value.symbol,
                }
            }


            let idents = idents;

            // all of this works out sine the root span is the span 0..0
            // which exists in all strings, and resolves to the empty string
            let required_cap = idents
                .iter()
                .map(|ident| ident.span.end - ident.span.start)
                .reduce(|last_ident_len, ident_len| last_ident_len + 2 + ident_len)
                .expect("idents should never be empty");

            let mut symbol = String::with_capacity(required_cap);

            let mut iter = idents.iter();

            if let Some(start) = iter.next() {
                let resolve = |ident: &Spanned<Ident>| &source.contents()[ident.span.into_range()];
                symbol += resolve(start);
                for ident in iter {
                    symbol += "::";
                    symbol += resolve(ident)
                }
            }

            let symbol = compiler.intern(&symbol);

            Self {
                symbol,
                // idents: MinSizedCowArray::from_vec(idents).expect("path always contains at least one ident"),
            }
        })
    }
}

mod sealed {
    use crate::compile::interner;

    pub trait Sealed {
        fn symbol(&self) -> interner::Symbol;
    }
}


pub trait Symbol: sealed::Sealed {}

impl sealed::Sealed for interner::Symbol {
    fn symbol(&self) -> interner::Symbol {
        *self
    }
}

impl<S: sealed::Sealed> Symbol for S {}


macro_rules! symbol_based {
    ($($ty:ty)+) => {
        $(
        impl PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                self.symbol == other.symbol
            }
        }
        
        impl Eq for $ty {}
        
        impl Hash for $ty {
            fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
                state.write_usize(string_interner::Symbol::to_usize(self.symbol))
            }
        }
        
        impl sealed::Sealed for $ty {
            fn symbol(&self) -> interner::Symbol {
                self.symbol
            }
        }
        )+
    };
}

symbol_based!(Ident Path);

// this should always be cheap, this is a very hot path
impl PartialEq<Ident> for Path {
    fn eq(&self, other: &Ident) -> bool {
        self.symbol == other.symbol
    }
}