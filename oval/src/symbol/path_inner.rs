use crate::compile::Spanned;
use crate::compile::interner::Interner;
use crate::compile::source::Source;
use crate::symbol::{Ident, Symbol};
use alloc::boxed::Box;
use alloc::string::String;
use alloc::sync::Arc;
use core::ptr::NonNull;
use std::mem::ManuallyDrop;

pub(super) trait ResolvableIdent {
    type Extra<'a>;

    fn value(&self) -> Ident;

    fn resolve<'ext>(&self, interner: &'ext Interner, ext: &'ext Self::Extra<'_>) -> &'ext str {
        let _ = ext;
        interner.resolve(self.value())
    }

    fn len(&self, interner: &Interner, ext: &Self::Extra<'_>) -> Option<usize> {
        let _ = (interner, ext);
        None
    }

    fn collect(this: &[Self]) -> Arc<[Ident]>
    where
        Self: Sized,
    {
        this.iter().map(Self::value).collect()
    }
}

pub(super) struct FromFile(pub(super) Spanned<Ident>);

impl ResolvableIdent for FromFile {
    type Extra<'a> = Source<'a>;

    fn value(&self) -> Ident {
        self.0.value
    }

    fn resolve<'ext>(&self, _: &'ext Interner, source: &'ext Source<'_>) -> &'ext str {
        &source.contents()[self.0.span.into_range()]
    }

    fn len(&self, _: &Interner, _: &Source<'_>) -> Option<usize> {
        Some(self.0.span.end - self.0.span.start)
    }
}

impl ResolvableIdent for Ident {
    type Extra<'a> = ();

    fn value(&self) -> Ident {
        *self
    }

    fn collect(this: &[Self]) -> Arc<[Ident]>
    where
        Self: Sized,
    {
        // mem-copy
        Arc::<[Ident]>::from(this)
    }
}

pub struct PathInner {
    /// this is used as the storage for the symbol
    /// and also used when there is no array of idents
    symbol_ident: Ident,
    /// tagged in the low bit
    /// low bit set = root path
    /// low bit cleared = relative path
    idents: *const [Ident],
}

// Safety: `idents` is just a tagged Arc under the hood
unsafe impl Send for PathInner {}
unsafe impl Sync for PathInner {}

// internal impl
impl PathInner {
    pub(super) fn construct_inline(ident: Ident) -> Self {
        Self {
            symbol_ident: ident,
            idents: core::ptr::slice_from_raw_parts(core::ptr::null::<Ident>(), 0),
        }
    }

    pub(super) fn construct_alloc<I: ResolvableIdent>(
        root: bool,
        symbol: Symbol,
        idents: &[I],
    ) -> Self {
        assert!(!idents.is_empty());

        let symbol_ident = Ident { symbol };

        let arc = I::collect(idents);

        let ptr = unsafe {
            NonNull::new_unchecked(Arc::into_raw(arc).cast_mut()).map_addr(|addr| {
                // the low bit should be cleared, since Ident is aligned to at least 2
                core::hint::assert_unchecked(addr.get() & 1 == 0);
                addr | (root as usize)
            })
        };

        Self {
            symbol_ident,
            idents: ptr.as_ptr(),
        }
    }

    pub(super) fn symbol(&self) -> Symbol {
        self.symbol_ident.symbol
    }

    pub fn is_root(&self) -> bool {
        (self.idents.addr() & 1) != 0
    }

    pub fn make_root(self, interner: &mut Interner) -> Self {
        if self.is_root() {
            return self;
        }

        let previous = interner.resolve(self.symbol());
        let mut new = String::with_capacity(previous.len() + 2);
        new += "::";
        new += previous;
        let symbol = interner.intern(&new);

        let this = ManuallyDrop::new(self);
        Self {
            symbol_ident: Ident { symbol },
            idents: this.idents.map_addr(|addr| addr | 1),
        }
    }

    pub fn make_relative(self, interner: &mut Interner) -> Self {
        if !self.is_root() {
            return self;
        }

        let previous = interner.resolve(self.symbol());
        unsafe {
            debug_assert!(previous.starts_with("::"));
            debug_assert!(previous.len() > 3);
            core::hint::assert_unchecked(previous.len() > 3);
        }
        let non_root = Box::<str>::from(&previous[2..]);
        let symbol = interner.intern(&non_root);

        let this = ManuallyDrop::new(self);
        Self {
            symbol_ident: Ident { symbol },
            // Safety:
            // check Self::as_arc_ptr
            idents: this.idents.map_addr(|addr| addr & const { !1 }),
        }
    }

    fn as_arc_ptr(&self) -> Option<NonNull<[Ident]>> {
        NonNull::new(self.idents.map_addr(|addr| addr & const { !1 }).cast_mut())
    }

    pub fn idents(&self) -> &[Ident] {
        match self.as_arc_ptr() {
            // Safety: this points to a previous allocation
            Some(array) => unsafe { array.as_ref() },
            None => core::slice::from_ref(&self.symbol_ident),
        }
    }

    pub fn first(&self) -> Ident {
        // Safety:
        // there is always at least one ident in the path, always
        unsafe { *self.idents().first().unwrap_unchecked() }
    }

    pub fn last(&self) -> Ident {
        // Safety:
        // there is always at least one ident in the path, always
        unsafe { *self.idents().last().unwrap_unchecked() }
    }

    pub fn split_first(&self) -> (Ident, &[Ident]) {
        // Safety:
        // there is always at least one ident in the path, always
        let (first, rest) = unsafe { self.idents().split_first().unwrap_unchecked() };

        (*first, rest)
    }

    pub fn split_last(&self) -> (&[Ident], Ident) {
        // Safety:
        // there is always at least one ident in the path, always
        let (last, rest) = unsafe { self.idents().split_last().unwrap_unchecked() };
        (rest, *last)
    }
}

impl Clone for PathInner {
    fn clone(&self) -> Self {
        if let Some(ptr) = self.as_arc_ptr() {
            unsafe { Arc::increment_strong_count(ptr.as_ptr()) }
        }

        Self {
            symbol_ident: self.symbol_ident,
            idents: self.idents,
        }
    }
}

impl Drop for PathInner {
    fn drop(&mut self) {
        if let Some(ptr) = self.as_arc_ptr() {
            // Safety:
            // the pointer made by self is just a pointer returned by Arc::into_raw
            unsafe { Arc::decrement_strong_count(ptr.as_ptr()) }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::compile::interner::Interner;

    #[test]
    fn round_trip() {
        let mut interner = Interner::new();
        let foo = interner.register_path("   foo   ").unwrap();
        let foo_root = foo.clone().make_root(&mut interner);
        let rooted_foo = interner.register_path(":: foo").unwrap();
        let unrooted_foo = rooted_foo.clone().make_relative(&mut interner);

        assert_eq!(foo_root, rooted_foo);
        assert_eq!(unrooted_foo, foo);
        assert_eq!(interner.resolve(&foo_root), interner.resolve(&rooted_foo));
        assert_eq!(interner.resolve(&unrooted_foo), interner.resolve(&foo));
    }
}
