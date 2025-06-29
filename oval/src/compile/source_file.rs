use alloc::string::String;
use crate::compile::tokenizer::TokenizedSource;
use crate::path::Path;


#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct SourceId(pub(crate) usize);

// FIXME: change Debug
#[derive(Debug)]
pub struct SourceFile {
    id: SourceId,
    module: Path, 
    contents: String,
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