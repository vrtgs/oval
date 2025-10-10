use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use ariadne::Report;
use crate::interner::Interner;
use crate::mir::OvalIR;
use crate::parser::{ParseErrors, ParseResult};
use crate::spanned::Span;

mod ast_id;
mod type_check;


enum CompileErrorReason {

}

pub struct CompileError(Box<CompileErrorReason>);

struct CompileErrorsInner {
    compile_errors: Vec<CompileError>,
    parse_errors: Option<ParseErrors>
}

pub struct CompileErrors(Box<CompileErrorsInner>);

impl CompileErrors {
    pub fn reports(&self) -> impl Iterator<Item=Report<'_, Span>> {
        let parser_reports = self
            .0
            .parse_errors
            .iter()
            .flat_map(|err| err.reports());

        let compiler_reports = self
            .0
            .compile_errors
            .iter()
            .map(|err| {
                match *err.0 {  }
            });

        parser_reports.chain(compiler_reports)
    }
}


mod sealed {
    use crate::ast::OvalModule;
    use crate::interner::Interner;
    use crate::parser::ParseResult;

    pub trait Sealed {
        fn into_parse_result(self, interner: &mut Interner) -> ParseResult;
    }

    impl<T: crate::parser::ParseOvalModule> Sealed for T {
        fn into_parse_result(self, interner: &mut Interner) -> ParseResult {
            crate::parser::parse(interner, self)
        }
    }

    impl Sealed for ParseResult {
        fn into_parse_result(self, _interner: &mut Interner) -> ParseResult {
            self
        }
    }

    impl Sealed for OvalModule {
        fn into_parse_result(self, _interner: &mut Interner) -> ParseResult {
            ParseResult {
                module: self,
                errors: None,
            }
        }
    }
}

pub trait Compilable: sealed::Sealed {}
impl<T: sealed::Sealed> Compilable for T {}


#[inline(never)] // don't inline for each version fo compile()
fn compile_inner(_interner: &mut Interner, mut module: ParseResult) -> Result<OvalIR, CompileErrors> {
    if let Some(parse_errors) = module.errors.take_if(|err| err.has_fatal_errors()) {
        return Err(CompileErrors(Box::new(CompileErrorsInner {
            compile_errors: vec![],
            parse_errors: Some(parse_errors),
        })));
    }

    let parse_errors = module.errors;
    let _module = module.module;

    if parse_errors.is_some() {
        return Err(CompileErrors(Box::new(CompileErrorsInner {
            compile_errors: vec![],
            parse_errors,
        })))
    }

    todo!()
}


pub fn compile<T: Compilable>(interner: &mut Interner, module: T) -> Result<OvalIR, CompileErrors> {
    let result = module.into_parse_result(interner);
    compile_inner(interner, result)
}

pub fn verify<T: Compilable>(interner: &mut Interner, module: T) -> Result<(), CompileErrors> {
    compile(interner, module).map(drop)
}
