use crate::compile::error::Result;
use crate::compile::tokenizer::TokenizedSource;
use crate::symbol::Path;
use alloc::borrow::Cow;
use alloc::rc::Rc;
use alloc::string::String;
use core::fmt::{Debug, Formatter};
use std::ops::Deref;

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct SourceId(pub(crate) usize);

pub(crate) enum Contents<'a> {
    #[expect(dead_code)]
    InnerModule {
        // invariants:
        // * source.0.content is either Contents::Borrowed or Contents::Owned
        // * start..end is valid and able to slice source.0.content
        source: Source<'a>,
        start: usize,
        end: usize,
        depth: usize,
    },
    Borrowed(&'a str),
    Owned(String),
}

impl<'a> From<Cow<'a, str>> for Contents<'a> {
    fn from(value: Cow<'a, str>) -> Self {
        match value {
            Cow::Borrowed(str) => Contents::Borrowed(str),
            Cow::Owned(string) => Contents::Owned(string),
        }
    }
}

impl<'a> Deref for Contents<'a> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        match *self {
            Contents::InnerModule {
                ref source,
                start,
                end,
                ..
            } => {
                unsafe {
                    let root_contents = match source.0.contents {
                        Contents::InnerModule { .. } => core::hint::unreachable_unchecked(),
                        Contents::Borrowed(str) => str,
                        Contents::Owned(ref str) => str,
                    };
                    // the contents of a source are NEVER modified
                    // and this was previously checked to be a valid range
                    root_contents.get_unchecked(start..end)
                }
            }
            Contents::Borrowed(str) => str,
            Contents::Owned(ref str) => str,
        }
    }
}

struct SourceInner<'a> {
    id: SourceId,
    module: Path,
    contents: Contents<'a>,
}

#[derive(Clone)]
pub struct Source<'a>(Rc<SourceInner<'a>>);

impl Debug for Source<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SourceFile")
            .field("id", self.id())
            .field("module", self.module())
            .finish_non_exhaustive()
    }
}

impl<'a> Source<'a> {
    pub(crate) fn new(id: SourceId, module: Path, contents: impl Into<Cow<'a, str>>) -> Self {
        Self(Rc::new(SourceInner {
            id,
            module,
            contents: Contents::from(contents.into()),
        }))
    }

    pub fn id(&self) -> &SourceId {
        &self.0.id
    }

    pub fn module(&self) -> &Path {
        &self.0.module
    }

    pub fn contents(&self) -> &str {
        &self.0.contents
    }

    pub fn tokenize(self) -> Result<'a, TokenizedSource<'a>> {
        TokenizedSource::new(self)
    }
}

impl AsRef<str> for Source<'_> {
    fn as_ref(&self) -> &str {
        self.contents()
    }
}
