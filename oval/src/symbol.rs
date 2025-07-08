use string_interner::Symbol as _;
use core::hash::Hash;
use alloc::string::String;
use crate::compile::error::SyntaxError;
use crate::compile::interner;
use crate::compile::parser::{DisAllowTrailing, ParseAst, Parser};
use crate::compile::span::SimpleSpan;
use crate::compile::tokenizer::TokenKind;


#[derive(Copy, Clone, Debug)]
pub struct Ident {
    span: SimpleSpan,
    symbol: interner::Symbol
}

impl Ident {
    pub fn len(&self) -> usize {
        self.span.end() - self.span.start()
    }
}

impl ParseAst for Ident {
    fn parse_inner<'a>(parser: &mut Parser<'a, '_, '_>) -> crate::compile::error::Result<'a, Self> {
        let token = parser.eat(TokenKind::Ident)?;
        let file = parser.file();
        let span = token.span();
        let symbol = parser.compiler().intern(span.into_full(file).slice());

        Ok(Self {
            span,
            symbol
        })
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

impl ParseAst for Path {
    fn parse_inner<'a>(parser: &mut Parser<'a, '_, '_>) -> crate::compile::error::Result<'a, Self> {
        let root = parser.maybe_eat(TokenKind::DoubleColon).is_some();
        let mut idents = parser.parse_list::<Ident, DisAllowTrailing>(TokenKind::DoubleColon)?;
        if idents.is_empty() {
            let mut expected = [TokenKind::DoubleColon, TokenKind::Ident].into_iter();
            // if root was provided
            // don't suggest root
            if root {
                let _ = expected.next();
            }
            return Err(parser.syntax_error(
                SyntaxError::expected_found(expected, parser.peek())
            ))
        }
        if root {
            let root_ident = Ident {
                span: SimpleSpan::EMPTY,
                symbol: parser.compiler().intern("{{root}}")
            };

            idents.insert(0, root_ident)
        }

        let idents = idents;

        if let [ident] = &*idents {
            return Ok(Path {
                symbol: ident.symbol,
            })
        }

        let mut symbol = String::with_capacity(
            root as usize * 2 +
                idents.iter().skip(root as usize).map(|ident| ident.len()).sum::<usize>()
        );

        let mut iter = idents.iter();

        if root {
            symbol += "::";
            iter.next();
        }
        if let Some(start) = iter.next() {
            let file = parser.file();
            let resolve = |ident: &Ident| ident.span.into_full(file).slice();
            symbol += resolve(start);
            for ident in iter {
                symbol += "::";
                symbol += resolve(ident)
            }
        }

        let symbol = parser.compiler().intern(&symbol);

        Ok(Self {
            symbol,
            // idents: MinSizedCowArray::from_vec(idents).expect("path always contains at least one ident"),
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