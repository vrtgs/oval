use alloc::boxed::Box;
use alloc::vec::Vec;
use alloc::borrow::ToOwned;
use core::fmt::{Debug, Display};
use ariadne::{Cache, Label, Report, ReportKind, Source};
use hashbrown::hash_map::Entry;
use hashbrown::HashMap;
use thin_vec::{thin_vec, ThinVec};
use crate::compile::source_file::{SourceFile, SourceId};
use crate::compile::span::{FullSpan, SimpleSpan};
pub use syntax::SyntaxError;
use crate::compile::compiler::Compiler;
use crate::compile::source_map::SourceMap;

pub mod syntax;

pub(crate) enum ErrorKind<'a> {
    Syntax { 
        source: &'a SourceFile,
        errors: Vec<SyntaxError>
    },
}

pub struct Error<'a>(ThinVec<ErrorKind<'a>>);

impl<'a> Error<'a> {
    pub fn syntax_error(file: &'a SourceFile, errors: impl IntoIterator<Item=SyntaxError>) -> Self {
        Self::from(ErrorKind::Syntax {
            source: file,
            errors: errors.into_iter().collect(),
        })
    }
}

impl<'a, E: Into<ErrorKind<'a>>> From<E> for Error<'a> {
    fn from(value: E) -> Self {
        Self(thin_vec![value.into()])
    }
}

impl<'a> Error<'a> {
    /// returns an iterator over required ids and report
    pub fn error_reports(&self) -> impl Iterator<Item=Report<'_, FullSpan>> {
        let errors = self.0.iter().flat_map(|error| {
            match error {
                ErrorKind::Syntax { source: file, errors} => {
                    let errors_iter = errors.iter().map(|error| {
                        let report_span = error.span().unwrap_or(SimpleSpan::EMPTY).into_full(file);

                        let report = Report::build(ReportKind::Error, report_span)
                            .with_code(1);

                        let report = match error.span() {
                            None => report.with_message(&error),
                            Some(span) => {
                                let span = span.into_full(file);
                                report
                                    .with_message("parse failure")
                                    .with_label({
                                        Label::new(span).with_message(&error)
                                    })
                            }
                        };

                        report.finish()
                    });

                    errors_iter
                }
            }
        });

        errors
    }
    
    pub fn merge(self, other: Self) -> Self {
        let mut errors = self.0;
        errors.extend(other.0);
        Self(errors)
    }
}

pub type Result<'a, T, E = Error<'a>> = core::result::Result<T, E>;

pub struct ErrorCache<'a> {
    source_map: &'a SourceMap,
    cache: Option<HashMap<usize, Source<&'a str>>>
}

impl<'a> ErrorCache<'a> {
    pub fn new(source_map: &'a SourceMap) -> Self {
        Self {
            source_map,
            cache: None
        }
    }
}

impl<'a> Cache<SourceId> for (&mut ErrorCache<'a>, &Compiler) {
    type Storage = &'a str;

    fn fetch(&mut self, id: &SourceId) -> core::result::Result<&Source<Self::Storage>, impl Debug> {
        let (this, _) = self;
        Ok(match this.cache.get_or_insert_default().entry(id.0) {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let Some(source) = this.source_map.get_module_by_id(id) else {
                    return Err(Box::new(alloc::format!("unknown source id '{:?}'", id)))
                };

                entry.insert(Source::from(source.contents()))
            }
        })
    }

    fn display<'b>(&self, id: &'b SourceId) -> Option<impl Display + 'b> {
        self.0.source_map.get_module_by_id(id).map(move |file| {
            self.1.resolve(file.module()).to_owned()
        })
    }
}
