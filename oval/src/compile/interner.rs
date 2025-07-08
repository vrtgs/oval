use core::fmt::{Debug, Formatter};
use string_interner::backend::StringBackend;
use string_interner::StringInterner;
use string_interner::symbol::SymbolUsize;

pub type Symbol = SymbolUsize;

pub(crate) struct Interner(StringInterner<StringBackend<Symbol>>);

impl Interner {
    pub fn new() -> Self {
        Self(StringInterner::new())
    }
    
    pub fn intern(&mut self, str: &str) -> Symbol {
        self.0.get_or_intern(str)
    }

    pub fn try_resolve(&self, symbol: Symbol) -> Option<&str> {
        self.0.resolve(symbol)
    }

    pub fn resolve(&self, symbol: Symbol) -> &str {
        self.try_resolve(symbol).expect("invalid symbol passed to interner")
    }
}

impl Debug for Interner {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Interner").finish_non_exhaustive()
    }
}