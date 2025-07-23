use crate::compile::hir::scoped::{Definition, LookupFailure, Scope};
use crate::compile::interner::Interner;
use crate::compile::syntax;
use crate::symbol::Path;
use alloc::rc::Rc;
use alloc::vec::Vec;

pub struct FunctionSignature {
    arguments: Vec<Type>,
    ret: Type,
}

#[derive(Clone)]
pub enum Type {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    Str,
    Path(Path),
    Array(Rc<Type>),
    Tuple(Rc<[Type]>),
}

pub enum UnknownType {
    InferenceFailed,
    PathInvalid(LookupFailure),
}

impl Type {
    pub fn resolve(
        scope: &Scope,
        ty: &syntax::r#type::Type,
        interner: &mut Interner,
    ) -> Result<Self, UnknownType> {
        let mut ty = ty;

        loop {
            break Ok(match ty {
                syntax::r#type::Type::Tuple(vic) => {
                    let tuple = vic
                        .iter()
                        .map(|ty| Self::resolve(scope, ty, interner))
                        .collect::<Result<Rc<[_]>, _>>()?;
                    Self::Tuple(tuple)
                }
                syntax::r#type::Type::Parens(inner) => {
                    ty = inner;
                    continue;
                }
                syntax::r#type::Type::Array(ty) => {
                    Self::Array(Rc::new(Self::resolve(scope, ty, interner)?))
                }
                syntax::r#type::Type::Path(path) => scope
                    .lookup(path, interner)
                    .and_then(|(path, def)| match def {
                        Definition::Type(..) => Ok(Self::Path(path)),
                        _ => Err(LookupFailure::PathInvalid {
                            path,
                            expected: "type",
                            found: def.name(),
                        }),
                    })
                    .or_else(|fail| {
                        Ok(match interner.resolve(path) {
                            "i8" => Self::I8,
                            "i16" => Self::I16,
                            "i32" => Self::I32,
                            "i64" => Self::I64,
                            "u8" => Self::U8,
                            "u16" => Self::U16,
                            "u32" => Self::U32,
                            "u64" => Self::U64,
                            "str" => Self::Str,
                            _ => return Err(fail),
                        })
                    })
                    .map_err(UnknownType::PathInvalid)?,
                syntax::r#type::Type::Infer => break Err(UnknownType::InferenceFailed),
            });
        }
    }
}
