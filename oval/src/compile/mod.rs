use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::ptr::NonNull;
use ariadne::{Label, Report, ReportKind};
use crate::ast::{FunctionSignature, Item, OvalModule, Type};
use crate::ast::recursive::Recursive;
use crate::hashed::HashMap;
use crate::interner::{Interner, Symbol};
use crate::parser::{ParseErrors, ParseResult};
use crate::spanned::{Span, Spanned};

pub enum CompileErrorReason {
    DuplicateItem {
        previous_declaration: Span,
        redeclaration: Span,
        name: Box<str>,
    },
    UnknownType {
        at: Span,
        name: Box<str>
    },
}

pub struct CompileError(Box<CompileErrorReason>);

struct CompileErrorsInner {
    compile_errors: Vec<CompileError>,
    parse_error: Option<ParseErrors>
}

pub struct CompileErrors(Box<CompileErrorsInner>);


impl CompileErrors {
    pub fn reports(&self)-> impl Iterator<Item=Report<'_, Span>> {
        let parser_reports = self
            .0
            .parse_error
            .iter()
            .flat_map(|parse_errs| {
                parse_errs.reports()
            });

        let new_reports = self
            .0
            .compile_errors
            .iter()
            .map(|err| {
                match *err.0 {
                    CompileErrorReason::DuplicateItem {
                        previous_declaration,
                        redeclaration,
                        ref name,
                    } => {
                        let name = &**name;

                        Report::build(ReportKind::Error, redeclaration)
                            .with_message(format_args!("the name `{name}` is defined multiple times"))
                            .with_labels([
                                Label::new(previous_declaration)
                                    .with_message(format_args!("previous definition of the value `{name}` here")),
                                Label::new(redeclaration)
                                    .with_message(format_args!("`{name}` redefined here"))
                            ])
                            .finish()
                    },
                    CompileErrorReason::UnknownType {
                        at,
                        ref name
                    } => {
                        let name = &**name;
                        Report::build(ReportKind::Error, at)
                            .with_message("unknown type")
                            .with_label(
                                Label::new(at)
                                    .with_message(format_args!("unknown type `{name}` ")),
                            )
                            .finish()
                    }
                }
            });

        parser_reports.chain(new_reports)
    }
}


// #[derive(Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
// #[repr(transparent)]
// struct AstId<'a, T> {
//     addr: usize,
//     _marker: PhantomData<Pin<&'a T>>
// }
//
// impl<'a, T> AstId<'a, T> {
//     #[expect(dead_code)]
//     pub fn new(ast_node: Pin<&'a T>) -> Self {
//         let reference: &T = &*ast_node;
//         Self {
//             addr: (reference as *const T).addr(),
//             _marker: PhantomData
//         }
//     }
// }


#[derive(Debug)]
pub(crate) enum ResolvedType {
    Usize,
    U64,
    U32,
    U16,
    U8,

    Isize,
    I64,
    I32,
    I16,
    I8,


    Str,
    Char,
    
    F64,
    F32,

    Never,

    List(Recursive<ResolvedType>),
    Tuple(Recursive<[ResolvedType]>),
    Fn(Recursive<(Box<[ResolvedType]>, ResolvedType)>)
}

impl ResolvedType {
    pub const UNIT: Self = {
        let ptr = core::ptr::slice_from_raw_parts_mut(
            core::ptr::dangling_mut::<ResolvedType>(),
            0
        );

        let ptr = NonNull::new(ptr)
            .expect("dangling pointers should never be null");

        // all ZST pointers are valid box pointers
        let tuple = unsafe { Recursive::from_ptr(ptr) };

        ResolvedType::Tuple(tuple)
    };

    pub fn is_unit(&self) -> bool {
        matches!(self, ResolvedType::Tuple(tuple) if tuple.get_ref().is_empty())
    }
}


#[derive(Debug)]
enum InferType {
    Resolved(ResolvedType),
    Integer,
    Error
}


struct SemanticAnalyzer<'a> {
    module: &'a OvalModule,
    interner: &'a Interner,
    items: HashMap<Symbol, &'a Item>,
    constant_types: HashMap<Symbol, ResolvedType>,
    errors: Vec<CompileError>,
}

impl SemanticAnalyzer<'_> {
    // this should be called under recurse
    // or Recursive::with_inner
    fn resolve_tuple(
        &mut self,
        types: &[Type],
    ) -> Result<Box<[ResolvedType]>, CompileError> {
        types.iter().map(|ty| self.resolve_type(ty)).collect()
    }

    pub fn resolve_signature(
        &mut self,
        signature: &FunctionSignature
    ) -> Result<ResolvedType, CompileError> {
        let args = signature
            .args
            .0
            .iter()
            .map(|(_, _, ty)| self.resolve_type(ty))
            .collect::<Result<_, CompileError>>()?;

        let ret = match &signature.ret {
            None => ResolvedType::UNIT,
            Some((_, ty)) => self.resolve_type(ty)?,
        };

        Ok(ResolvedType::Fn(Recursive::new((args, ret))))
    }

    pub fn resolve_type(
        &mut self,
        mut ty: &Type,
    ) -> Result<ResolvedType, CompileError> {
        loop {
            return match ty {
                Type::Never(_) => Ok(ResolvedType::Never),
                Type::Ident(ident) => {
                    Ok(match ident.symbol() {
                        Symbol::USIZE => ResolvedType::Usize,
                        Symbol::U64 => ResolvedType::U64,
                        Symbol::U32 => ResolvedType::U32,
                        Symbol::U16 => ResolvedType::U16,
                        Symbol::U8 => ResolvedType::U8,

                        Symbol::ISIZE => ResolvedType::Isize,
                        Symbol::I64 => ResolvedType::I64,
                        Symbol::I32 => ResolvedType::I32,
                        Symbol::I16 => ResolvedType::I16,
                        Symbol::I8 => ResolvedType::I8,
                        
                        Symbol::STR => ResolvedType::Str,
                        Symbol::CHAR => ResolvedType::Char,
                        
                        Symbol::F64 => ResolvedType::F64,
                        Symbol::F32 => ResolvedType::F32,

                        symbol => {
                            let name = self.interner.resolve(symbol);
                            return Err(CompileError(Box::new(CompileErrorReason::UnknownType {
                                at: ty.span(),
                                name: Box::from(name)
                            })))
                        },
                    })
                },
                Type::Array(_) => {
                    todo!("evaluate constants")
                }
                Type::List(list) => list.with_inner(|ty| {
                    self.resolve_type(&ty.0)
                        .map(Recursive::new)
                        .map(ResolvedType::List)
                }),
                Type::Parens(paren) => {
                    ty = &paren.get_ref().0;
                    continue
                },
                Type::Tuple(tuple) => tuple.with_inner(|ty| {
                    let tuple = self.resolve_tuple(&ty.0)?;
                    Ok(ResolvedType::Tuple(Recursive::from_box(tuple)))
                }),
                Type::Fn(func) => func.with_inner(|(_kw_fn, args, ret)| {
                    let args = self.resolve_tuple(&args.0)?;
                    let ret = match ret {
                        None => ResolvedType::UNIT,
                        Some((_arrow, ty)) => self.resolve_type(ty)?,
                    };

                    Ok(ResolvedType::Fn(Recursive::new((args, ret))))
                })
            }
        }
    }

    pub fn analyze(
        module: &OvalModule,
        interner: &Interner
    ) -> Vec<CompileError> {
        let mut this = SemanticAnalyzer {
            module,
            interner,
            items: HashMap::default(),
            constant_types: HashMap::default(),
            errors: vec![]
        };

        for item in this.module.items.iter() {
            let get_name = |item: &Item| match item {
                Item::Function(func) => func.signature.name,
                Item::Const(const_item) => const_item.name,
            };

            let this_decl = get_name(item);
            let this_name = this_decl.symbol();
            if let Err(insert) = this.items.try_insert(this_name, item) {
                let name = Box::<str>::from(this.interner.resolve(this_decl.symbol()));
                let prev_decl = get_name(insert.entry.get());

                this.errors.push(CompileError(Box::new(CompileErrorReason::DuplicateItem {
                    previous_declaration: prev_decl.span(),
                    redeclaration: this_decl.span(),
                    name,
                })))
            }


            let ty = match item {
                Item::Function(f) => this.resolve_signature(&f.signature),
                Item::Const(const_item) => this.resolve_type(&const_item.ty),
            };

            let ty = ty.unwrap_or_else(|err| {
                this.errors.push(err);
                ResolvedType::Never
            });

            let ret = this.constant_types.insert(this_name, ty);
            assert!(ret.is_none())
        }

        this.errors
    }
}



// TODO rethink this API
pub fn verify(module: ParseResult, interner: &mut Interner) -> Result<OvalModule, CompileErrors> {
    if module.has_fatal_errors() {
        debug_assert!(module.errors.is_some());
        return Err(CompileErrors(Box::new(CompileErrorsInner {
            compile_errors: vec![],
            parse_error: module.errors,
        })));
    }

    let parse_error = module.errors;
    let module = module.module;

    let compile_errors = SemanticAnalyzer::analyze(
        &module,
        interner
    );

    if parse_error.is_some() || !compile_errors.is_empty() {
        return Err(CompileErrors(Box::new(CompileErrorsInner {
            compile_errors,
            parse_error,
        })))
    }


    Ok(module)
}