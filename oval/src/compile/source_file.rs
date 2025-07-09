use alloc::borrow::Cow;
use core::fmt::{Debug, Formatter};
use crate::compile::tokenizer::TokenizedSource;
use crate::symbol::Path;
use crate::compile::error::Result;


#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct SourceId(pub(crate) usize);

pub struct SourceFile<'a> {
    id: SourceId,
    module: Path,
    contents: Cow<'a, str>
}

impl Debug for SourceFile<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SourceFile")
            .field("id", &self.id)
            .field("module", &self.module)
            .finish_non_exhaustive()
    }
}

impl<'a> SourceFile<'a> {
    pub(crate) fn new(id: usize, module: Path, contents: impl Into<Cow<'a, str>>) -> Self {
        Self {
            id: SourceId(id),
            module,
            contents: contents.into()
        }
    }
    
    
    pub fn id(&self) -> &SourceId {
        &self.id
    }
    
    pub fn module(&self) -> &Path {
        &self.module
    }
    
    pub fn contents(&self) -> &str {
        &self.contents
    }

    pub fn tokenize(&self) -> Result<TokenizedSource> {
        TokenizedSource::new(self)
    }
}


impl AsRef<str> for SourceFile<'_> {
    fn as_ref(&self) -> &str {
        self.contents()
    }
}