use crate::compile::syntax::parse_str;
use crate::symbol::{Ident, Path, SymbolLike};
use core::fmt::{Debug, Formatter};
use string_interner::StringInterner;
use string_interner::backend::BucketBackend;
use string_interner::symbol::SymbolUsize;
use thiserror::Error;

pub type Symbol = SymbolUsize;

struct InternerInner(StringInterner<BucketBackend<Symbol>>);

impl InternerInner {
    pub fn new() -> Self {
        Self(StringInterner::new())
    }

    pub fn intern_static(&mut self, str: &'static str) -> Symbol {
        self.0.get_or_intern_static(str)
    }

    pub fn intern(&mut self, str: &str) -> Symbol {
        self.0.get_or_intern(str)
    }

    pub fn try_resolve(&self, symbol: Symbol) -> Option<&str> {
        self.0.resolve(symbol)
    }

    pub fn resolve(&self, symbol: Symbol) -> &str {
        self.try_resolve(symbol)
            .expect("invalid symbol passed to interner")
    }
}

pub struct Interner(InternerInner);

impl Debug for Interner {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Interner").finish_non_exhaustive()
    }
}

#[derive(Debug, Error)]
#[error("invalid path, failed to parse")]
pub struct InvalidPath(());

#[derive(Debug, Error)]
#[error("invalid identifier, failed to parse")]
pub struct InvalidIdent(());

impl Interner {
    pub fn new() -> Self {
        Self(InternerInner::new())
    }

    #[must_use]
    pub fn intern_static(&mut self, str: &'static str) -> Symbol {
        self.0.intern_static(str)
    }

    #[must_use]
    pub fn intern(&mut self, str: &str) -> Symbol {
        self.0.intern(str)
    }

    #[must_use]
    pub fn resolve<S: SymbolLike>(&self, symbol: S) -> &str {
        self.0.resolve(symbol.symbol())
    }

    pub fn register_path(&mut self, path: &str) -> Result<Path, InvalidPath> {
        parse_str::<Path>(path, self).ok_or(InvalidPath(()))
    }

    pub fn register_ident(&mut self, ident: &str) -> Result<Ident, InvalidIdent> {
        parse_str::<Ident>(ident, self).ok_or(InvalidIdent(()))
    }
}
