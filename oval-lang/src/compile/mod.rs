use crate::interner::Interner;
use crate::mir::OvalIR;
use crate::parser::{ParseErrors, ParseResult};
use crate::spanned::{Span, Spanned};
use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use alloc::{format, vec};
use ariadne::{Label, Report, ReportKind};
use core::fmt::Display;

mod ast_id;
mod build_hir;

enum CompileErrorReason {
    NotFound(Box<str>),
    Custom {
        label: &'static str,
        message: String,
    },
}

struct CompileErrorInner {
    span: Span,
    reason: CompileErrorReason,
}

impl CompileErrorInner {
    pub fn header(&self) -> impl Display {
        match self.reason {
            CompileErrorReason::NotFound(ref name) => {
                Cow::Owned(format!("cannot find type `{name}` in this scope"))
            }
            CompileErrorReason::Custom { label, .. } => Cow::Borrowed(label),
        }
    }

    pub fn messages(&self) -> impl Iterator<Item = Label<Span>> {
        let message = match self.reason {
            CompileErrorReason::NotFound(_) => "not found in this scope",
            CompileErrorReason::Custom { ref message, .. } => message,
        };

        [Label::new(self.span).with_message(message)].into_iter()
    }
}

pub(crate) struct CompileError(Box<CompileErrorInner>);

impl CompileError {
    fn new(span: Span, reason: CompileErrorReason) -> Self {
        Self(Box::new(CompileErrorInner { span, reason }))
    }

    pub fn name_not_found(span: Span, name: &str) -> CompileError {
        CompileError::new(span, CompileErrorReason::NotFound(Box::from(name)))
    }

    pub fn custom(span: Span, label: &'static str, message: impl ToString) -> CompileError {
        CompileError::new(
            span,
            CompileErrorReason::Custom {
                label,
                message: message.to_string(),
            },
        )
    }
}

impl Spanned for CompileError {
    fn span(&self) -> Span {
        self.0.span
    }
}

struct CompileErrorsInner {
    compile_errors: Vec<CompileError>,
    parse_errors: Option<ParseErrors>,
}

pub struct CompileErrors(Box<CompileErrorsInner>);

impl CompileErrors {
    pub fn reports(&self) -> impl Iterator<Item = Report<'_, Span>> {
        let parser_reports = self.0.parse_errors.iter().flat_map(|err| err.reports());

        let compiler_reports = self.0.compile_errors.iter().map(|err| {
            let builder = Report::build(ReportKind::Error, err.span());
            builder
                .with_message(err.0.header())
                .with_labels(err.0.messages())
                .finish()
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
fn compile_inner(
    _interner: &mut Interner,
    mut module: ParseResult,
) -> Result<OvalIR, CompileErrors> {
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
        })));
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
