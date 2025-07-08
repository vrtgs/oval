use core::fmt::{Debug, Formatter};
use alloc::borrow::ToOwned;
use thiserror::Error;
use crate::compile::error::Result;
use crate::compile::interner;
use crate::compile::interner::Interner;
use crate::compile::parser::{ParseAst, Parser};
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


    pub fn intern(&mut self, str: &str) -> interner::Symbol {
        self.interner.intern(str)
    }

    pub fn resolve<S: Symbol>(&self, symbol: &S) -> &str {
        self.interner.resolve(symbol.symbol())
    }


    pub fn register_path(&mut self, path: &str) -> Result<Path, InvalidPath> {
        let file = SourceFile::new(0, Path::invalid(), path.to_owned());
        let stream = file
            .tokenize()
            .into_stream()
            .map_err(|_| InvalidPath(()))?;

        let mut parser = Parser::new(self, &stream);
        let path = Path::parse_inner(&mut parser).map_err(|_| InvalidPath(()))?;
        parser.hit_eos().then_some(path).ok_or(InvalidPath(()))
    }
}

impl Debug for Compiler {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("CompileContext").finish_non_exhaustive()
    }
}
