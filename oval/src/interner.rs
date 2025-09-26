use crate::hashed::HashMap;
use alloc::boxed::Box;
use alloc::vec::Vec;
use alloc::vec;
use core::borrow::Borrow;
use cfg_if::cfg_if;
use core::fmt::{Debug, Formatter};
use core::hash::{Hash, Hasher};
use core::num::NonZero;
use core::ptr::NonNull;
use hashbrown::hash_map::EntryRef;

cfg_if! {
    if #[cfg(target_pointer_width = "16")] {
        type InnerSymbol = u16;
    } else {
        type InnerSymbol = u32;
    }
}

#[inline(always)]
const fn symbol_to_usize(symbol_inner: InnerSymbol) -> usize {
    const { assert!(usize::BITS >= InnerSymbol::BITS) }

    symbol_inner as usize
}

const fn usize_to_symbol(symbol_inner: usize) -> InnerSymbol {
    const {
        assert!(InnerSymbol::MIN == 0 && InnerSymbol::BITS <= usize::BITS);
    }

    // casting InnerSymbol::MAX as usize is valid
    // this is because usize is always at least as big as InnerSymbol if not bigger
    if symbol_inner > InnerSymbol::MAX as usize {
        panic!("invalid symbol")
    }

    symbol_inner as InnerSymbol
}

#[derive(Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
#[repr(transparent)]
pub struct Symbol(NonZero<InnerSymbol>);

impl Debug for Symbol {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("Symbol").finish_non_exhaustive()
    }
}

enum InternedStr {
    Static(&'static str),
    Boxed(Box<str>)
}

impl InternedStr {
    #[inline(always)]
    pub const fn as_str(&self) -> &str {
        match *self {
            InternedStr::Static(str) => str,
            InternedStr::Boxed(ref boxed) => boxed,
        }
    }

    #[inline(always)]
    pub const fn stable_ptr(&self) -> NonNull<str> {
        NonNull::from_ref(self.as_str())
    }
}

impl Hash for InternedStr {
    #[inline(always)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        <str as Hash>::hash(self.as_str(), state)
    }
}

impl Eq for InternedStr {}

impl PartialEq for InternedStr {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        <str as PartialEq>::eq(self.as_str(), other.as_str())
    }

    #[inline(always)]
    fn ne(&self, other: &Self) -> bool {
        <str as PartialEq>::ne(self.as_str(), other.as_str())
    }
}

impl Borrow<str> for InternedStr {
    #[inline(always)]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl From<&str> for InternedStr {
    fn from(value: &str) -> Self {
        InternedStr::Boxed(Box::from(value))
    }
}


pub struct Interner {
    interned: Vec<NonNull<str>>,
    map: HashMap<InternedStr, Symbol>,
}


impl Default for Interner {
    fn default() -> Self {
        Self::new()
    }
}



macro_rules! declare_static_symbols {
    (@make_unit $x: expr) => { () };

    (
        {
            $(
            index: $index: expr;
            $_symbol_name: ident = $_symbol: literal;
            )*
        }
        $symbol_name: ident = $symbol: literal;
        $($rest: tt)*
    ) => {
        declare_static_symbols! {
            {
                $(
                index: $index;
                $_symbol_name = $_symbol;
                )*

                index: usize_to_symbol(<[()]>::len(&[$(declare_static_symbols!(@make_unit $index)),*]));
                $symbol_name = $symbol;
            }
            $($rest)*
        }
    };
    (
        {
            $(
            index: $index: expr;
            $symbol_name: ident = $symbol: literal;
            )*
        }

    ) => {
        impl Symbol {
            $(pub(crate) const $symbol_name: Self = {
                Self(NonZero::new($index + 1).unwrap())
            };)*
        }


        impl Interner {
            pub fn new() -> Self {
                $(const $symbol_name: &str = $symbol;)*

                // make sure there are no duplicates
                const {
                    const SYMBOLS: &[&str] = &[$($symbol_name),*];

                    const fn str_eq(a: &str, b: &str) -> bool {
                        let a = a.as_bytes();
                        let b = b.as_bytes();

                        if a.len() != b.len() {
                            return false;
                        }

                        let mut len = a.len();
                        while len > 0 {
                            len -= 1;
                            if a[len] != b[len] {
                                return false
                            }
                        }

                        true
                    }

                    let mut i = 0;
                    while i < SYMBOLS.len() {
                        let mut j = 0;
                        while j < SYMBOLS.len() {
                            if i == j {
                                j += 1;
                                continue
                            }
                            if str_eq(SYMBOLS[i], SYMBOLS[j]) {
                                panic!("duplicate static symbols detected")
                            }

                            j += 1;
                        }

                        i += 1;
                    }
                }


                let interned = vec![
                    $(const { NonNull::from_ref($symbol_name) }),*
                ];

                #[allow(unused_mut)]
                let mut map = HashMap::with_capacity_and_hasher(
                    <[Symbol]>::len(&[ $(Symbol::$symbol_name),* ]),
                    ahash::RandomState::default()
                );

                $(
                    let previous_val = map.insert(InternedStr::Static($symbol_name), Symbol::$symbol_name);
                    // Safety: all static symbols are unique
                    unsafe { core::hint::assert_unchecked(previous_val.is_none()) }
                )*

                Self {
                    interned,
                    map,
                }
            }
        }


        #[cfg(test)]
        mod test_static_symbols {
            use super::*;

            #[test]
            fn resolves() {
                let interner = Interner::new();

                $(
                    assert_eq!(
                        interner.resolve(Symbol::$symbol_name),
                        $symbol
                    );
                )+
            }
        }
    };

    (
        $($symbol_name: ident = $symbol: literal;)*
    ) => {
        declare_static_symbols! {
            {}
            $($symbol_name = $symbol;)*
        }
    };
}


declare_static_symbols! {
    USIZE = "usize";
    U64 = "u64";
    U32 = "u32";
    U16 = "u16";
    U8 = "u8";

    ISIZE = "isize";
    I64 = "i64";
    I32 = "i32";
    I16 = "i16";
    I8 = "i8";

    STR = "str";
    CHAR = "char";

    F64 = "f64";
    F32 = "f32";
}

impl Interner {
    pub fn get_or_try_intern(&mut self, str: &str) -> Option<Symbol> {
        Some(match self.map.entry_ref(str) {
            EntryRef::Occupied(exists) => *exists.get(),
            EntryRef::Vacant(slot) => {
                // make sure OOM happens before any insertion
                self.interned.try_reserve(1).ok()?;

                // checked_add should always succeed,
                // since the maximum allocation is always <= isize::MAX for non ZSTs
                // but logically this is the case; and since it gets optimized out either way
                // this is fine

                let slot_number = self.interned.len().checked_add(1)?;
                let slot_numer = InnerSymbol::try_from(slot_number).ok()?;
                let symbol = Symbol(
                    NonZero::new(slot_numer)
                        .expect("slot_number must be > 1 since it was added to"),
                );
                let entry = slot.insert_entry(symbol);

                let ptr = entry.key().stable_ptr();

                // we should always have enough capacity to do this
                self.interned.push(ptr);
                *entry.get()
            }
        })
    }

    pub fn get_or_intern(&mut self, str: &str) -> Symbol {
        self.get_or_try_intern(str)
            .unwrap_or_else(|| panic!("ran out of symbols"))
    }

    pub fn resolve(&self, symbol: Symbol) -> &str {
        let idx = symbol_to_usize(symbol.0.get() - 1);
        let ptr = self
            .interned
            .get(idx)
            .copied()
            .expect("symbols passed to resolve should come from the same interner");

        // Safety: Box has a stable address, and entries from the map are never removed
        // and the reference lives only as long as self, guaranteeing that the key still exists
        unsafe { ptr.as_ref() }
    }
}

impl Debug for Interner {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Interner").finish_non_exhaustive()
    }
}
