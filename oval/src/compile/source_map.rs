use crate::compile::interner::Interner;
use crate::compile::source::{Source, SourceId};
use crate::symbol::Path;
use alloc::borrow::Cow;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::convert::Infallible;
use core::fmt::{Debug, Display, Formatter};
use hashbrown::hash_map::Entry;
use hashbrown::{HashMap, HashSet};
use std::cell::{Ref, RefCell};
use thiserror::Error;

pub struct CompileContextBuilder<'a> {
    module_names: HashMap<Path, SourceId>,
    collisions: HashSet<Path>,
    modules: Vec<Source<'a>>,
}

#[derive(Debug, Error)]
pub struct ConflictingModules<'a> {
    interner: &'a Interner,
    collisions: HashSet<Path>,
}

impl Display for ConflictingModules<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.collisions.len() {
            0 => unreachable!(),
            1 => write!(
                f,
                "duplicate module {:?}",
                self.interner
                    .resolve(self.collisions.iter().next().unwrap())
            ),
            2.. => {
                f.write_str("duplicate modules ")?;
                f.debug_set()
                    .entries(self.collisions.iter().map(|x| self.interner.resolve(x)))
                    .finish()
            }
        }
    }
}

impl<'a> CompileContextBuilder<'a> {
    fn add_module_inner<E>(
        &mut self,
        module: Path,
        contents: impl FnOnce() -> Result<String, E>,
    ) -> Result<(), E> {
        let id = SourceId(self.modules.len());

        if self.module_names.insert(module.clone(), id).is_some() {
            self.collisions.insert(module);
            return Ok(());
        }

        if self.collisions.is_empty() {
            self.modules.push(Source::new(id, module, contents()?));
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
            ({ reader }).read_to_string(&mut contents).map(|_| contents)
        })?;
        Ok(this)
    }

    #[cfg(feature = "std")]
    pub fn file_module(
        self,
        module: Path,
        path: impl AsRef<std::path::Path>,
    ) -> std::io::Result<Self> {
        self.read_module(module, std::fs::File::open(path)?)
    }

    pub fn build<'c>(
        self,
        interner: &'c Interner,
    ) -> Result<SourceMap<'a>, ConflictingModules<'c>> {
        if !self.collisions.is_empty() {
            return Err(ConflictingModules {
                interner,
                collisions: self.collisions,
            });
        }

        Ok(SourceMap(Rc::new(RefCell::new(SourceMapInner {
            module_names: self.module_names,
            modules: self.modules,
        }))))
    }
}

struct SourceMapInner<'a> {
    module_names: HashMap<Path, SourceId>,
    modules: Vec<Source<'a>>,
}

#[derive(Clone)]
pub struct SourceMap<'a>(Rc<RefCell<SourceMapInner<'a>>>);

#[allow(private_interfaces)]
mod sealed {
    use crate::compile::source::SourceId;
    use crate::compile::source_map::SourceMapInner;
    use crate::symbol::Path;

    /// # Safety:
    /// SourceId returned must be valid
    /// unexpected panics may occur otherwise
    pub unsafe trait Sealed {
        fn get_id(&self, source_map: &SourceMapInner) -> Option<SourceId>;
    }

    unsafe impl Sealed for Path {
        fn get_id(&self, source_map: &SourceMapInner) -> Option<SourceId> {
            // if its in the map, then it exists inside modules
            source_map.module_names.get(self).copied()
        }
    }

    unsafe impl Sealed for SourceId {
        fn get_id(&self, source: &SourceMapInner) -> Option<SourceId> {
            (self.0 < source.modules.len()).then_some(*self)
        }
    }

    unsafe impl<S: Sealed> Sealed for &S {
        fn get_id(&self, source_map: &SourceMapInner) -> Option<SourceId> {
            <S as Sealed>::get_id(*self, source_map)
        }
    }
}

pub trait ModuleId: sealed::Sealed {}

impl<S: sealed::Sealed> ModuleId for S {}

impl<'a> SourceMap<'a> {
    pub fn builder() -> CompileContextBuilder<'a> {
        CompileContextBuilder {
            module_names: HashMap::new(),
            collisions: HashSet::new(),
            modules: vec![],
        }
    }

    pub fn modules(&self) -> impl Iterator<Item = Source<'a>> {
        let mut index = 0;
        core::iter::from_fn(move || {
            let module = self.get_module(SourceId(index))?;
            index += 1;
            Some(module)
        })
    }

    pub fn insert_module<'c>(
        &self,
        interner: &'c Interner,
        module: Path,
        contents: impl Into<Cow<'a, str>>,
    ) -> Result<(), ConflictingModules<'c>> {
        pub fn insert_module_inner<'b, 'c>(
            this: &SourceMap<'b>,
            interner: &'c Interner,
            module: Path,
            contents: Cow<'b, str>,
        ) -> Result<(), ConflictingModules<'c>> {
            let mut this = this.0.borrow_mut();
            let id = SourceId(this.modules.len());
            let module2 = module.clone();

            match this.module_names.entry(module) {
                Entry::Occupied(_) => {
                    return Err(ConflictingModules {
                        interner,
                        collisions: HashSet::from([module2]),
                    });
                }
                Entry::Vacant(empty) => {
                    empty.insert(id);
                }
            }

            this.modules.push(Source::new(id, module2, contents));

            Ok(())
        }

        insert_module_inner(self, interner, module, contents.into())
    }

    fn get_module_inner<'s>(&'s self, id: impl ModuleId) -> Option<Ref<'s, Source<'a>>> {
        let this = self.0.borrow();
        Ref::filter_map(this, |this| {
            let id = id.get_id(&this)?;
            Some(&this.modules[id.0])
        })
        .ok()
    }

    #[must_use]
    pub fn get_module(&self, id: impl ModuleId) -> Option<Source<'a>> {
        self.get_module_inner(id).as_deref().map(Source::clone)
    }

    #[must_use]
    pub fn contains_module(&self, id: impl ModuleId) -> bool {
        self.get_module_inner(id).is_some()
    }
}
