use std::cell::RefCell;
use std::fmt::{Debug, Formatter};
use std::sync::Once;
use string_interner::{DefaultStringInterner, DefaultSymbol};


#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct Symbol(DefaultSymbol);

impl Debug for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Symbol")
            .field("text", &resolve(*self))
            .field("inner", &self.0)
            .finish_non_exhaustive()
    }
}

static ONE_INTERNER: Once = Once::new();

thread_local! {
    static INTERNER: RefCell<DefaultStringInterner> = {
        let mut init = false;
        ONE_INTERNER.call_once(|| {
            init = true;
        });

        assert!(init, "interner should not be used across threads");

        RefCell::new(DefaultStringInterner::new())
    };
}

pub fn intern_static(str: &'static str) -> Symbol {
    Symbol(INTERNER.with_borrow_mut(|interner| interner.get_or_intern_static(str)))
}

pub fn intern(str: &str) -> Symbol {
    Symbol(INTERNER.with_borrow_mut(|interner| interner.get_or_intern(str)))
}

pub fn resolve(symbol: Symbol) -> Box<str> {
    INTERNER.with_borrow(|interner| {
        interner
            .resolve(symbol.0)
            .map(Box::from)
            .expect("unresolved symbol passed to intern")
    })
}