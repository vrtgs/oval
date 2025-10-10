use core::fmt::Debug;
use core::ops::Range;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Span {
    start: usize,
    end: usize,
}

impl Span {
    #[inline]
    pub const fn new(start: usize, end: usize) -> Self {
        assert!(start <= end, "degenerate span");
        Self { start, end }
    }

    #[inline]
    pub const fn from_range(range: Range<usize>) -> Self {
        Self::new(range.start, range.end)
    }

    pub const fn into_range(self) -> Range<usize> {
        self.assert_invariants();

        self.start..self.end
    }

    #[inline(always)]
    const fn assert_invariants(&self) {
        // Safety: Span is always a non degenerate range
        unsafe { core::hint::assert_unchecked(self.start <= self.end) }
    }

    #[inline]
    pub const fn merge_strict(start: Self, end: Self) -> Self {
        start.assert_invariants();
        end.assert_invariants();

        Self::new(start.start, end.end)
    }

    #[inline]
    pub const fn merge(this: Self, that: Self) -> Self {
        this.assert_invariants();
        that.assert_invariants();

        // FIXME(const-hack) use min and max instead

        // get the smaller start
        let start = match this.start < that.start {
            true => this.start,
            false => that.start,
        };

        // and the bigger end
        let end = match this.end > that.end {
            true => this.end,
            false => that.end,
        };


        Self::new(start, end)
    }

    pub const fn start(&self) -> usize {
        self.assert_invariants();
        self.start
    }

    pub const fn end(&self) -> usize {
        self.assert_invariants();
        self.end
    }

    pub const fn len(&self) -> usize {
        self.assert_invariants();
        // Safety: Span is always a non degenerate range
        unsafe { self.end.unchecked_sub(self.start) }
    }

    pub const fn is_empty(&self) -> bool {
        self.assert_invariants();
        // since span is always a non degenerate range
        // its only empty if start == end
        // and there is no need to check
        // start > end since that is not possible
        self.start == self.end
    }
}

pub trait Spanned {
    fn span(&self) -> Span;
}


macro_rules! spanned_struct {
    ($field: ident in $ty: ty) => {
        impl $crate::spanned::Spanned for $ty {
            fn span(&self) -> Span {
                $crate::spanned::Spanned::span(&self.$field)
            }
        }
    };
    ($ty: ty) => {
        impl $crate::spanned::Spanned for $ty {
            fn span(&self) -> Span {
                self.span
            }
        }
    };
}

pub(crate) use spanned_struct;

impl chumsky::span::Span for Span {
    type Context = ();
    type Offset = usize;

    fn new((): Self::Context, mut range: Range<Self::Offset>) -> Self {
        if range.end < range.start {
            core::mem::swap(&mut range.end, &mut range.start)
        }

        Span::from_range(range)
    }

    fn context(&self) -> Self::Context {}

    #[inline(always)]
    fn start(&self) -> Self::Offset {
        Span::start(self)
    }

    #[inline(always)]
    fn end(&self) -> Self::Offset {
        Span::end(self)
    }

    fn union(&self, other: Self) -> Self
    where
        Self::Context: PartialEq + Debug,
        Self::Offset: Ord,
        Self: Sized,
    {
        Self::merge(*self, other)
    }
}

impl ariadne::Span for Span {
    type SourceId = ();

    fn source(&self) -> &Self::SourceId {
        &()
    }

    fn start(&self) -> usize {
        Span::start(self)
    }

    fn end(&self) -> usize {
        Span::end(self)
    }

    fn len(&self) -> usize {
        Span::len(self)
    }

    fn is_empty(&self) -> bool {
        Span::is_empty(self)
    }
}