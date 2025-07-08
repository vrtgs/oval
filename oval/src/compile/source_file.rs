use alloc::string::String;
use core::fmt::{Debug, Formatter};
use crate::compile::tokenizer::TokenizedSource;
use crate::symbol::Path;


#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct SourceId(pub(crate) usize);

pub struct SourceFile {
    id: SourceId,
    module: Path,
    contents: String,
}

impl Debug for SourceFile {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SourceFile")
            .field("id", &self.id)
            .field("module", &self.module)
            .finish_non_exhaustive()
    }
}

impl SourceFile {
    pub(crate) fn new(id: usize, module: Path, contents: String) -> Self {
        Self {
            id: SourceId(id),
            module,
            contents
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

    pub fn tokenize(&self) -> TokenizedSource {
        TokenizedSource::new(self)
    }
}


impl AsRef<str> for SourceFile {
    fn as_ref(&self) -> &str {
        self.contents()
    }
}