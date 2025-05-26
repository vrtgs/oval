use std::ops::Deref;
use parking_lot::{MappedRwLockReadGuard, RwLock, RwLockReadGuard};
use string_interner::DefaultStringInterner;
use string_interner::symbol::SymbolU32;

pub struct Interner(RwLock<DefaultStringInterner>);

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Symbol(SymbolU32);


#[derive(Debug)]
pub struct ResolvedSymbol<'a>(MappedRwLockReadGuard<'a, str>);

impl<'a> Deref for ResolvedSymbol<'a> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Interner {
    pub fn new() -> Self {
        Self(RwLock::new(DefaultStringInterner::new()))
    }

    pub fn interned(&self, str: &str) -> Symbol {
        if let Some(sym) = self.0.read().get(str) {
            return Symbol(sym)
        }

        Symbol(self.0.write().get_or_intern(str))
    }

    pub fn resolve(&self, symbol: Symbol) -> Option<ResolvedSymbol<'_>> {
        let guard = RwLockReadGuard::try_map(self.0.read(), |int| {
            int.resolve(symbol.0)
        }).ok();
        
        guard.map(ResolvedSymbol)
    }
}