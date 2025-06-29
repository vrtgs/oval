use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::vec::Vec;
use ariadne::{Label, Report, ReportKind};
use crate::compile::source_file::SourceFile;
use crate::compile::span::{FullSpan, SimpleSpan};

pub(crate) struct SyntaxError {
    pub(crate) span: SimpleSpan,
    pub(crate) message: Cow<'static, str>
}

pub(crate) enum ErrorKind<'a> {
    Syntax { 
        source: &'a SourceFile,
        errors: Vec<SyntaxError>
    }
}

pub struct Error<'a>(Box<ErrorKind<'a>>);

impl<'a> From<ErrorKind<'a>> for Error<'a> {
    fn from(value: ErrorKind<'a>) -> Self {
        Self(Box::new(value))
    }
}

impl<'a> Error<'a> {
    /// returns an iterator over required ids and report
    pub fn error_reports(&self) -> impl Iterator<Item=Report<'_, FullSpan>> {
        let errors = match &*self.0 {
            ErrorKind::Syntax { source: file, errors} => {
                let errors_iter = errors.iter().map(|error| {
                    let span = error.span.into_full(file);
                    
                    let report = Report::build(ReportKind::Error, span)
                        .with_code(1)
                        .with_message("tokenization failure")
                        .with_label({
                            Label::new(span).with_message(&*error.message)
                        })
                        .finish();

                    report
                });
                errors_iter
            }
        };

        errors.into_iter()
    }
}

pub type Result<'a, T> = core::result::Result<T, Error<'a>>;