use crate::arena::{make_handle, AnyInterner};
use compact_str::CompactString;
use core::fmt::{Debug, Formatter};

macro_rules! static_str {
    ($str: literal) => {
        const { CompactString::const_new($str) }
    };
}

make_handle! {
    pub Symbol for str: !Sized;
    internable { InternAs = CompactString };
    with constants {
        pub USIZE = static_str!("usize");
        pub U64 = static_str!("u64");
        pub U32 = static_str!("u32");
        pub U16 = static_str!("u16");
        pub U8 = static_str!("u8");

        pub ISIZE = static_str!("isize");
        pub I64 = static_str!("i64");
        pub I32 = static_str!("i32");
        pub I16 = static_str!("i16");
        pub I8 = static_str!("i8");

        pub STR = static_str!("str");
        pub CHAR = static_str!("char");
        pub BOOL = static_str!("bool");

        pub F64 = static_str!("f64");
        pub F32 = static_str!("f32");

        pub WILD_CARD = static_str!("_");
    }
}

pub struct Interner(AnyInterner<str>);


impl Default for Interner {
    fn default() -> Self {
        Self::new()
    }
}

impl Interner {
    pub fn new() -> Self {
        Self(AnyInterner::new())
    }

    pub fn get_or_intern(&mut self, item: &str) -> Symbol {
        self.0.get_or_intern_ref(item)
    }

    pub fn try_resolve(&self, symbol: Symbol) -> Option<&str> {
        self.0.try_resolve(symbol)
    }

    pub fn resolve(&self, symbol: Symbol) -> &str {
        self.try_resolve(symbol)
            .expect("symbols passed to resolve should come from the same interner")
    }
}

impl Debug for Interner {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Interner")
            .field("size", &self.0.len())
            .finish_non_exhaustive()
    }
}
