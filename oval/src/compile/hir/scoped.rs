use crate::compile::hir::r#type::{FunctionSignature, Type};
use crate::compile::interner::Interner;
use crate::compile::syntax::item::Visibility;
use crate::symbol::{Ident, Path};
use alloc::borrow::Cow;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::cell::RefCell;
use hashbrown::{HashMap, HashSet};
use std::vec;

#[derive(Clone)]
pub enum Definition {
    Function(Rc<FunctionSignature>),
    Global {
        mutable: bool,
        ty: Type,
        initialized: bool,
    },
    Type(Type),
    Scope {
        scope: Scope,
    },
}

impl Definition {
    pub fn name(&self) -> &'static str {
        match self {
            Definition::Function(_) => "function",
            Definition::Global { .. } => "global",
            Definition::Type(_) => "type",
            Definition::Scope { .. } => "scope",
        }
    }
}

enum Meta {
    Root,
    Child { name: Ident, parent: Scope },
}

pub struct ScopeInner {
    contents: RefCell<HashMap<Ident, (Visibility, Definition)>>,
    meta: Meta,
}

#[derive(Clone)]
pub struct Scope(Rc<ScopeInner>);

#[derive(Debug)]
pub enum LookupFailure {
    PathNotFound(Path),
    PathPrivate(Path),
    PathInvalid {
        path: Path,
        expected: &'static str,
        found: &'static str,
    },
}

impl Scope {
    #[allow(clippy::needless_lifetimes)] // false positive
    fn traverse_up<'a>(&'a self, mut func: impl FnMut(&'a Scope, Ident)) {
        #[cfg(debug_assertions)]
        let mut visited = HashSet::new();

        let mut parent = self;
        while let Meta::Child {
            parent: ref new_parent,
            name,
        } = parent.0.meta
        {
            #[cfg(debug_assertions)]
            {
                assert!(
                    visited.insert(Rc::as_ptr(&parent.0).addr()),
                    "Scope cycle detected; Scopes should be trees (acyclical)"
                )
            }
            func(new_parent, name);
            parent = new_parent;
        }
    }

    fn absolute_path(&self) -> Vec<Ident> {
        let mut absolute_path = vec![];
        self.traverse_up(|_, name| absolute_path.push(name));
        absolute_path.reverse();
        absolute_path
    }

    fn lookup_inner(
        mut this: &Self,
        path: &Path,
        interner: &mut Interner,
    ) -> Result<(Path, Definition), LookupFailure> {
        let lookup_root = path.is_root();

        enum LookupPathPrefix {
            AlreadyRoot(Path),
            Constructing(Vec<Ident>),
        }

        let mut path_prefix: LookupPathPrefix = match lookup_root {
            true => {
                let mut root = this;
                this.traverse_up(|parent, _| root = parent);
                this = root;
                LookupPathPrefix::AlreadyRoot(path.clone())
            }
            false => match this.absolute_path() {
                vec if vec.is_empty() => {
                    LookupPathPrefix::AlreadyRoot(path.clone().make_root(interner))
                }
                path => LookupPathPrefix::Constructing(path),
            },
        };

        let (walk_path, lookup) = path.split_last();

        let mut this = Cow::Borrowed(this);
        for (i, ident) in walk_path.iter().enumerate() {
            if let LookupPathPrefix::Constructing(ref mut idents) = path_prefix {
                idents.push(*ident)
            }

            let mut make_fail_path = || {
                let idents = match &path_prefix {
                    LookupPathPrefix::AlreadyRoot(path) => &path.idents()[..=i],
                    LookupPathPrefix::Constructing(vec) => vec,
                };

                Path::from_idents(true, idents, interner)
            };

            let contents_ref = this.0.contents.borrow();
            let content = contents_ref.get(ident);
            let def = match content {
                Some((Visibility::Public, definition)) => definition,
                Some((Visibility::Private, _)) => {
                    return Err(LookupFailure::PathPrivate(make_fail_path()));
                }
                None => return Err(LookupFailure::PathNotFound(make_fail_path())),
            };

            let inner_scope = match def {
                Definition::Scope { scope } => scope.clone(),
                def => {
                    return Err(LookupFailure::PathInvalid {
                        path: make_fail_path(),
                        expected: "scope",
                        found: def.name(),
                    });
                }
            };

            drop(contents_ref);
            this = Cow::Owned(inner_scope)
        }

        let absolute_path = match path_prefix {
            LookupPathPrefix::AlreadyRoot(path) => path,
            LookupPathPrefix::Constructing(mut vec) => {
                vec.push(lookup);
                Path::from_idents(true, &vec, interner)
            }
        };

        let ref_content = this.0.contents.borrow();
        let definition = ref_content.get(&lookup);

        match definition {
            None => Err(LookupFailure::PathNotFound(absolute_path)),
            // if this is an inner scope, and we got a private item, that is no good
            Some((Visibility::Private, _)) if matches!(this, Cow::Owned(_)) => {
                Err(LookupFailure::PathPrivate(absolute_path))
            }
            Some((_, def)) => Ok((absolute_path, def.clone())),
        }
    }

    pub fn lookup(
        &self,
        path: &Path,
        interner: &mut Interner,
    ) -> Result<(Path, Definition), LookupFailure> {
        Self::lookup_inner(self, path, interner)
    }
}
