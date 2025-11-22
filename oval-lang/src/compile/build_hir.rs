use crate::ast::recursive::Recursive;
use crate::ast::{IntegerType, OvalModule, Type as AstType};
use crate::compile::CompileError;
use crate::compile::build_hir::signature::FunctionSignature;
use crate::interner::{Interner, Symbol};
use crate::spanned::Span;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::pin::Pin;

mod signature;

pub struct TypeVar(usize);

pub enum Type {
    Var(TypeVar),
    Never,
    Int(IntegerType),
    Str,
    Char,
    Bool,
    Tuple(Recursive<[Type]>),
    List(Recursive<Type>),
    Fn(Recursive<FunctionSignature>),
}

impl Type {
    pub const UNIT: Self = Type::Tuple(Recursive::empty_slice());
}

pub enum TypeContext {
    FunctionBody { inference_counter: usize },
    ItemPosition,
}

pub struct HirBuilder<'ast, 'interner, 'err> {
    ast: Pin<&'ast OvalModule>,
    errors: &'err mut Vec<CompileError>,
    interner: &'interner mut Interner,
}

const X: usize = 3;
const Y: [u8; X] = [3; X];
const Z: usize = Y[0] as usize;

const fn foo(x: [u8; X]) -> [u8; Z] {
    x
}

impl HirBuilder<'_, '_, '_> {
    pub fn parse_function_signature(
        &mut self,
        contex: &mut TypeContext,
        args: &[AstType],
        ret: Option<&AstType>,
    ) -> Result<Type, ()> {
        let mut new_ty = Vec::with_capacity(args.len() + 1);

        for arg in args {
            new_ty.push(self.parse_ast_ty(contex, arg)?)
        }

        new_ty.push(ret.map_or(Ok(Type::UNIT), |ty| self.parse_ast_ty(contex, ty))?);

        let new_ty = new_ty.into_boxed_slice();
        let new_ty = FunctionSignature::from_box(new_ty);
        let signature = Recursive::from_box(new_ty);
        Ok(Type::Fn(signature))
    }

    pub fn parse_ast_ty(&mut self, contex: &mut TypeContext, ty: &AstType) -> Result<Type, ()> {
        let mut loop_ty = ty;
        loop {
            let ty = loop_ty;
            break Ok(match ty {
                AstType::Never(_) => Type::Never,
                AstType::Ident(ident) => match ident.symbol {
                    Symbol::USIZE => Type::Int(IntegerType::Usize),
                    Symbol::U64 => Type::Int(IntegerType::U64),
                    Symbol::U32 => Type::Int(IntegerType::U32),
                    Symbol::U16 => Type::Int(IntegerType::U16),
                    Symbol::U8 => Type::Int(IntegerType::U8),

                    Symbol::ISIZE => Type::Int(IntegerType::Isize),
                    Symbol::I64 => Type::Int(IntegerType::I64),
                    Symbol::I32 => Type::Int(IntegerType::I32),
                    Symbol::I16 => Type::Int(IntegerType::I16),
                    Symbol::I8 => Type::Int(IntegerType::I8),

                    Symbol::WILD_CARD => self.fresh_type(ident.span, contex)?,

                    _ => {
                        self.errors.push(CompileError::name_not_found(
                            ident.span,
                            self.interner.resolve(ident.symbol),
                        ));

                        return Err(());
                    }
                },
                AstType::Array(_) => todo!("array types not supported yet"),
                AstType::List(list) => list.with_inner(|inner| {
                    Type::List(Recursive::new(self.parse_ast_ty(contex, &inner.0)))
                }),
                AstType::Parens(ty) => {
                    loop_ty = &ty.get_ref().0;
                    continue;
                }
                AstType::Tuple(types) => types.with_inner(|ty| {
                    let types =
                        ty.0.iter()
                            .map(|ty| self.parse_ast_ty(contex, ty))
                            .collect::<Box<[Type]>>();

                    Type::Tuple(Recursive::from_box(types))
                }),
                AstType::Fn(func) => func.with_inner(|func| {
                    let (_kw_fn, args, ret) = func;
                    self.parse_function_signature(
                        contex,
                        &args.0,
                        ret.as_ref().map(|(_arrow, ty)| ty),
                    )
                }),
            });
        }
    }

    pub fn fresh_type(&mut self, span: Span, contex: &mut TypeContext) -> Result<Type, ()> {
        match contex {
            TypeContext::FunctionBody { inference_counter } => {
                let old = *inference_counter;
                *inference_counter = old + 1;
                Type::Var(TypeVar(old))
            }
            TypeContext::ItemPosition => {
                self.errors.push(CompileError::custom(
                    span,
                    "the placeholder `_` is not allowed within types on item signatures",
                    "not allowed in type signatures",
                ));
                return Err(());
            }
        }
    }

    pub fn build_ast(
        interner: &mut Interner,
        errors: &mut Vec<CompileError>,
        ast: &OvalModule,
    ) -> ! {
        let mut builder = HirBuilder {
            ast: Pin::new(ast),
            errors,
            interner,
        };

        todo!()
    }
}
