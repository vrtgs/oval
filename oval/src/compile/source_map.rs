use core::fmt::{Debug, Display, Formatter};
use core::convert::Infallible;
use alloc::vec::Vec;
use alloc::string::String;
use alloc::vec;
use hashbrown::{HashMap, HashSet};
use thiserror::Error;
use crate::compile::compiler::Compiler;
use crate::compile::source_file::{SourceFile, SourceId};
use crate::symbol::Path;

pub struct CompileContextBuilder<'a> {
    module_names: HashMap<Path, usize>,
    collisions: HashSet<Path>,
    modules: Vec<SourceFile<'a>>,
}

#[derive(Debug, Error)]
pub struct ConflictingModules<'a> {
    compiler: &'a Compiler,
    collisions: HashSet<Path>
}

impl Display for ConflictingModules<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.collisions.len() {
            0 => unreachable!(),
            1 => write!(f, "duplicate module {:?}", self.compiler.resolve(self.collisions.iter().next().unwrap())),
            2.. => {
                f.write_str("duplicate modules ")?;
                f
                    .debug_set()
                    .entries(self.collisions.iter().map(|x| self.compiler.resolve(x)))
                    .finish()
            }
        }
    }
}

impl<'a> CompileContextBuilder<'a> {
    fn add_module_inner<E>(&mut self, module: Path, contents: impl FnOnce() -> Result<String, E>) -> Result<(), E> {
        let id = self.modules.len();

        if self.module_names.insert(module.clone(), id).is_some() {
            self.collisions.insert(module);
            return Ok(())
        }

        if self.collisions.is_empty() {
            self.modules.push(SourceFile::new(id, module, contents()?));
        }

        Ok(())
    }

    pub fn add_module(self, module: Path, contents: String) -> Self {
        let mut this = self;
        let Ok(()) = this.add_module_inner(module, || Ok::<_, Infallible>(contents));
        this
    }

    #[cfg(feature = "std")]
    pub fn read_module(self, module: Path, reader: impl std::io::Read) -> std::io::Result<Self> {
        let mut this = self;
        this.add_module_inner(module, || {
            let mut contents = String::new();
            ({reader}).read_to_string(&mut contents).map(|_| contents)
        })?;
        Ok(this)
    }

    #[cfg(feature = "std")]
    pub fn file_module(self, module: Path, path: impl AsRef<std::path::Path>) -> std::io::Result<Self> {
        self.read_module(module, std::fs::File::open(path)?)
    }

    pub fn build(self, compiler: &Compiler) -> Result<SourceMap<'a>, ConflictingModules> {
        if !self.collisions.is_empty() {
            return Err(ConflictingModules {
                compiler,
                collisions: self.collisions
            })
        }

        Ok(SourceMap {
            module_names: self.module_names,
            modules: self.modules,
        })
    }
}

pub struct SourceMap<'a> {
    module_names: HashMap<Path, usize>,
    modules: Vec<SourceFile<'a>>,
}

impl<'a> SourceMap<'a> {
    pub fn builder() -> CompileContextBuilder<'a> {
        CompileContextBuilder {
            module_names: HashMap::new(),
            collisions: HashSet::new(),
            modules: vec![],
        }
    }

    pub fn modules(&self) -> impl Iterator<Item=&SourceFile> {
        self.modules.iter()
    }

    pub fn get_module(&self, path: &Path) -> Option<&SourceFile> {
        self.module_names.get(path).map(|&id| &self.modules[id])
    }

    pub fn get_module_by_id(&self, id: &SourceId) -> Option<&SourceFile> {
        self.modules.get(id.0)
    }
}
