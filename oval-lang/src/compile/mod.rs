use crate::compile::hir::ConstraintSpan;
use crate::compile::mir::{make_mir, Mir};
use crate::interner::Interner;
use crate::parser::{ParseErrors, ParseResult};
use crate::spanned::{Span, Spanned};
use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use alloc::{format, vec};
use ariadne::{Label, Report, ReportKind};
use core::fmt::Display;

mod hir;
mod mir;
mod algorithms;


#[derive(Debug)]
enum CompileErrorReason {
    ValueNotFound(Box<str>),
    TypeNotFound(Box<str>),
    Custom {
        label: Cow<'static, str>,
        message: String,
        second_message: Option<(Span, Cow<'static, str>)>,
    },
    RedefineError {
        old_definition: Span,
        name: Box<str>,
    },
    CycleDetected(Vec<Span>),
}

#[derive(Debug)]
struct CompileErrorInner {
    span: Span,
    reason: CompileErrorReason,
}

impl CompileErrorInner {
    pub fn header(&self) -> impl Display {
        match self.reason {
            CompileErrorReason::ValueNotFound(ref name) => {
                Cow::Owned(format!("cannot find value `{name}` in this scope"))
            }
            CompileErrorReason::TypeNotFound(ref name) => {
                Cow::Owned(format!("cannot find type `{name}` in this scope"))
            }
            CompileErrorReason::Custom { ref label, .. } => Cow::Borrowed(&**label),
            CompileErrorReason::RedefineError { ref name, .. } => {
                format!("the name `{name}` is defined multiple times").into()
            },
            CompileErrorReason::CycleDetected(_) => Cow::Borrowed("cycle detected")
        }
    }

    pub fn messages(&self) -> impl Iterator<Item = Label<Span>> {
        let labels = match self.reason {
            CompileErrorReason::ValueNotFound(_)
            | CompileErrorReason::TypeNotFound(_) => {
                vec![Label::new(self.span).with_message("not found in this scope")]
            }
            CompileErrorReason::Custom {
                label: _,
                ref message,
                ref second_message
            } => {
                let mut vec = Vec::with_capacity(1 + second_message.is_some() as usize);
                vec.push(
                    Label::new(self.span)
                        .with_message(message.as_str())
                        .with_priority(1)
                );

                if let &Some((span, ref msg)) = second_message {
                    let msg: &str = msg;
                    vec.push(Label::new(span).with_message(msg))
                }
                vec
            },
            CompileErrorReason::RedefineError {
                old_definition,
                ref name
            } => {
                let name: &str = name;
                let redefinition = self.span;
                vec![
                    Label::new(old_definition)
                        .with_message(format_args!("previous definition of the value `{name}` here")),
                    Label::new(redefinition)
                        .with_message(format_args!("`{name}` redefined here")),
                ]
            },
            CompileErrorReason::CycleDetected(ref cycle) => {
                let &[first, ref rest @ ..] = cycle.as_slice() else {
                    unreachable!()
                };

                let last = first;

                let mut vec = Vec::with_capacity(cycle.len());

                match rest {
                    [] => {
                        vec.push(Label::new(first).with_message("simplifying this constant"));
                        vec.push(Label::new(last).with_message("requires simplifying the same constant"));
                    },
                    rest => {
                        vec.push(Label::new(first).with_message("simplifying this constant"));
                        for (i, &span) in rest.iter().enumerate() {
                            let label = Label::new(span).with_message(format_args!(
                                "{}requires simplifying",
                                if i == 0 { "" } else { "which " }
                            ));
                            vec.push(label);
                        }
                        vec.push(Label::new(last).with_message("which again requires simplifying"));
                    }
                }

                vec
            }
        };

        labels.into_iter()
    }
}

#[derive(Debug)]
pub(crate) struct CompileError(CompileErrorInner);

impl CompileError {
    fn new(span: Span, reason: CompileErrorReason) -> Self {
        Self(CompileErrorInner { span, reason })
    }


    pub fn cycle_detected(cycle: Vec<Span>) -> CompileError {
        let &[first, ..] = cycle.as_slice() else {
            panic!("invalid cycle")
        };

        CompileError::new(first, CompileErrorReason::CycleDetected(cycle))
    }

    pub fn val_not_found(span: Span, name: &str) -> CompileError {
        CompileError::new(span, CompileErrorReason::ValueNotFound(Box::from(name)))
    }
    
    pub fn type_not_found(span: Span, ty: &str) -> CompileError {
        CompileError::new(span, CompileErrorReason::TypeNotFound(Box::from(ty)))
    }

    pub fn custom_full(
        span: Span,
        label: impl Into<Cow<'static, str>>,
        message: impl ToString,
        second_message: Option<(Span, impl Into<Cow<'static, str>>)>
    ) -> CompileError {
        CompileError::new(
            span,
            CompileErrorReason::Custom {
                label: label.into(),
                message: message.to_string(),
                second_message: second_message
                    .map(|(span, str)| (span, str.into()))
            },
        )
    }

    pub fn custom(span: Span, label: impl Into<Cow<'static, str>>, message: impl ToString) -> CompileError {
        CompileError::custom_full(
            span,
            label,
            message,
            None::<(Span, &'static str)>
        )
    }

    pub fn type_mismatch(loc: ConstraintSpan, expected: impl Display, found: impl Display) -> CompileError {
        let (span, second) = loc.as_two_spans();
        CompileError::custom_full(
            span,
            "Type Mismatch",
            format_args!("expected `{expected}`, found `{found}`"),
            second.map(|span| {
                (span, Cow::Borrowed("type declared here"))
            })
        )
    }

    pub fn duplicate_definition(
        name: &str,
        redefinition: Span,
        old_definition: Span,
    ) -> CompileError {
        CompileError::new(
            redefinition,
            CompileErrorReason::RedefineError {
                old_definition,
                name: name.into()
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

pub struct OvalProgram(Mir);

// dont instantiate a new compile() function for each parsable
#[inline(never)]
fn compile_inner(
    interner: &mut Interner,
    module_result: ParseResult,
) -> Result<OvalProgram, CompileErrors> {
    let mut parse_errors = module_result.errors;
    
    if let Some(ref error) = parse_errors && error.has_fatal_errors() {
        return Err(CompileErrors(Box::new(CompileErrorsInner {
            compile_errors: vec![],
            parse_errors: parse_errors.take(),
        })))
    }

    let module = module_result.module;
    let mut errors = vec![];
    let hir = hir::make_hir(
        interner,
        &mut errors,
        module
    );
    
    if let Ok(validated_hir) = hir::type_check_hir(interner, &mut errors, hir)
        && let Ok(mir) = make_mir(interner, &mut errors, validated_hir)
    {
        assert!(errors.is_empty());
        return Ok(OvalProgram(mir))
    }

    debug_assert!(!errors.is_empty());
    Err(CompileErrors(Box::new(CompileErrorsInner {
        compile_errors: errors,
        parse_errors,
    })))
}

pub fn compile<T: Compilable>(interner: &mut Interner, module: T) -> Result<OvalProgram, CompileErrors> {
    let result = module.into_parse_result(interner);
    compile_inner(interner, result)
}

pub fn verify<T: Compilable>(interner: &mut Interner, module: T) -> Result<(), CompileErrors> {
    compile(interner, module).map(drop)
}
