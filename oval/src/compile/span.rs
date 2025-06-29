use core::fmt::{Debug, Formatter};
use core::ops::Range;
use crate::compile::source_file::{SourceFile, SourceId};

/// Represents a span in a source file
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct SimpleSpan {
    start: usize,
    end: usize,
}

impl Debug for SimpleSpan {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        Debug::fmt(&self.into_range(), f)
    }
}


impl SimpleSpan {
    pub const fn from_range(range: Range<usize>) -> Self {
        Self {
            start: range.start,
            end: range.end
        }
    }

    pub const fn into_range(self) -> Range<usize> {
        self.start..self.end
    }

    pub const fn start(&self) -> usize {
        self.start
    }

    pub const fn end(&self) -> usize {
        self.end
    }

    pub fn into_full(self, file: &SourceFile) -> FullSpan {
        let span = FullSpan {
            span: self,
            file
        };

        let _ = span.slice();

        span
    }
}

impl From<SimpleSpan> for Range<usize> {
    fn from(value: SimpleSpan) -> Self {
        value.into_range()
    }
}

impl From<Range<usize>> for SimpleSpan {
    fn from(value: Range<usize>) -> Self {
        Self::from_range(value)
    }
}

// FIXME: fix Debug impl
#[derive(Debug, Copy, Clone)]
/// Represents a span in a source file, with access to the source file
pub struct FullSpan<'a> {
    span: SimpleSpan,
    file: &'a SourceFile
}

impl<'a> FullSpan<'a> {
    pub fn as_simple(&self) -> SimpleSpan {
        self.span
    }
    
    pub fn slice(&self) -> &'a str {
        &self.file.contents()[self.span.into_range()]
    }
}

impl ariadne::Span for FullSpan<'_> {
    type SourceId = SourceId;

    fn source(&self) -> &Self::SourceId { 
        self.file.id()
    }

    fn start(&self) -> usize {
        self.span.start()
    }

    fn end(&self) -> usize {
        self.span.end()
    }
}