use core::fmt::{Debug, Formatter};
use alloc::borrow::ToOwned;
use thiserror::Error;
use crate::compile::error::Result;
use crate::compile::interner;
use crate::compile::interner::Interner;
use crate::compile::parser::parse_from_source;
use crate::compile::source_file::SourceFile;
use crate::symbol::{Path, Symbol};

pub struct Compiler {
    pub(crate) interner: Interner
}

#[derive(Debug, Error)]
#[error("invalid path, failed to parse")]
pub struct InvalidPath(());

impl Compiler {
    pub fn new() -> Self {
        Self {
            interner: Interner::new()
        }
    }

    #[must_use]
    pub fn intern(&mut self, str: &str) -> interner::Symbol {
        self.interner.intern(str)
    }

    #[must_use]
    pub fn resolve<S: Symbol>(&self, symbol: &S) -> &str {
        self.interner.resolve(symbol.symbol())
    }


    pub fn register_path(&mut self, path: &str) -> Result<Path, InvalidPath> {
        let file = SourceFile::new(0, Path::invalid(), path.to_owned());
        let tokenized = file
            .tokenize()
            .map_err(|_| InvalidPath(()))?;

        parse_from_source::<Path>(tokenized, self).map_err(|_| InvalidPath(()))
    }
}

impl Debug for Compiler {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("CompileContext").finish_non_exhaustive()
    }
}
