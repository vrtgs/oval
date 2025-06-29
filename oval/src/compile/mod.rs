use alloc::string::{ToString, String};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt::{Debug, Display, Formatter};
use core::convert::Infallible;
use ariadne::{Cache, Source};
use hashbrown::{HashMap, HashSet};
use hashbrown::hash_map::Entry;
use thiserror::Error;
use crate::compile::source_file::{SourceFile, SourceId};
use crate::path::Path;

pub mod source_file;
pub mod tokenizer;
pub mod error;
pub mod span;
pub mod parser;


pub struct SourceMapBuilder {
    module_names: HashMap<Path, usize>,
    collisions: HashSet<Path>,
    modules: Vec<SourceFile>
}

#[derive(Debug, Error)]
pub struct ConflictingModules(HashSet<Path>);

impl Display for ConflictingModules {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.0.len() { 
            0 => unreachable!(),
            1 => write!(f, "duplicate module {}", self.0.iter().next().unwrap()),
            2.. => {
                write!(f, "duplicate module {:?}", self.0)
            }
        }
    }
}

impl SourceMapBuilder {
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

    pub fn build(self) -> Result<SourceMap, ConflictingModules> {
        if !self.collisions.is_empty() { 
            return Err(ConflictingModules(self.collisions))
        }
        
        Ok(SourceMap {
            module_names: self.module_names,
            modules: self.modules,
        })
    }
}

pub struct SourceMap {
    module_names: HashMap<Path, usize>,
    modules: Vec<SourceFile>,
}

impl SourceMap {
    pub fn builder() -> SourceMapBuilder {
        SourceMapBuilder {
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

pub struct SourceErrorCache<'a> {
    source: &'a SourceMap,
    cache: Option<HashMap<usize, Source<&'a str>>>
}

impl<'a> SourceErrorCache<'a> {
    pub fn new(source: &'a SourceMap) -> Self {
        Self {
            source,
            cache: None
        }
    }
}

impl<'a> Cache<SourceId> for SourceErrorCache<'a> {
    type Storage = &'a str;

    fn fetch(&mut self, id: &SourceId) -> Result<&Source<Self::Storage>, impl Debug> {
        Ok(match self.cache.get_or_insert_default().entry(id.0) {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let Some(source) = self.source.get_module_by_id(id) else {
                    return Err(alloc::boxed::Box::new(alloc::format!("Failed to fetch source '{:?}'", id)))
                };
                
                entry.insert(Source::from(source.contents()))
            }
        })
    }

    fn display<'b>(&self, id: &'b SourceId) -> Option<impl Display + 'b> {
        self.source.get_module_by_id(id).map(move |file| file.module().to_string())
    }
}