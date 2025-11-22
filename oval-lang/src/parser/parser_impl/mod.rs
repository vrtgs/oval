use crate::interner::Interner;
use crate::spanned::{Span, Spanned};
use crate::tokens::{TokenKind, TokenizerError};
use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use ariadne::{Label, Report, ReportKind};
use chumsky::DefaultExpected;
use chumsky::inspector::SimpleState;
use chumsky::label::LabelError;
use chumsky::util::MaybeRef;
use core::fmt::{Debug, Display, Formatter};

mod ast_impl;

pub mod ext;

pub(crate) use ext::{static_parser, static_parser_inner, static_unsized_parser};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum Pattern {
    Eof,
    Token(TokenKind),
    Label(&'static str),
    Any,
    SomethingElse,
}

impl<'a> From<DefaultExpected<'a, TokenKind>> for Pattern {
    fn from(expected: DefaultExpected<'a, TokenKind>) -> Self {
        match expected {
            DefaultExpected::Token(tok) => Self::Token(tok.into_inner()),
            DefaultExpected::Any => Self::Any,
            DefaultExpected::SomethingElse => Self::SomethingElse,
            DefaultExpected::EndOfInput => Self::Eof,
            _ => Self::SomethingElse,
        }
    }
}

impl From<TokenKind> for Pattern {
    fn from(value: TokenKind) -> Self {
        Pattern::Token(value)
    }
}

#[derive(Debug)]
pub(crate) enum SyntaxErrorReason {
    TokenizerError(TokenizerError),
    ExpectedFound {
        expected: BTreeSet<Pattern>,
        found: Option<TokenKind>,
        span: Span,
    },
    Custom {
        span: Span,
        label: Cow<'static, str>,
        message: String,
    },
    CustomLabeled {
        span: Span,
        label: Cow<'static, str>,
        labels: Vec<(Span, String)>,
    },
}

fn fmt_pattern(pattern: &Pattern, f: &mut Formatter<'_>) -> core::fmt::Result {
    let str = match *pattern {
        Pattern::Eof => "end of file",
        Pattern::Label(label) => label,
        Pattern::Any => "anything",
        Pattern::SomethingElse => "something else",
        Pattern::Token(token) => return Display::fmt(&token, f),
    };

    f.write_str(str)
}

impl Display for SyntaxErrorReason {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            SyntaxErrorReason::TokenizerError(err) => <TokenizerError as Display>::fmt(err, f),
            SyntaxErrorReason::Custom { message, .. } => f.write_str(message),
            SyntaxErrorReason::CustomLabeled { label, .. } => f.write_str(label),
            SyntaxErrorReason::ExpectedFound {
                expected, found, ..
            } => {
                f.write_str("expected ")?;
                let mut iter = expected.iter();
                match iter.next().map(|pat| (pat, iter.next())) {
                    None => f.write_str("something")?,
                    Some((one, None)) => fmt_pattern(one, f)?,
                    Some((one, Some(last))) => {
                        match iter.next() {
                            // one of
                            Some(first_list) => {
                                f.write_str("one of ")?;
                                fmt_pattern(one, f)?;
                                for pattern in Some(first_list).into_iter().chain(iter) {
                                    f.write_str(", ")?;
                                    fmt_pattern(pattern, f)?;
                                }
                            }
                            // its just this or that
                            None => fmt_pattern(one, f)?,
                        }

                        f.write_str(" or ")?;
                        fmt_pattern(last, f)?;
                    }
                }

                f.write_str(" found ")?;
                f.write_str(found.map_or("end of file", TokenKind::name))
            }
        }
    }
}

impl SyntaxErrorReason {
    pub fn label(&self) -> &str {
        match *self {
            SyntaxErrorReason::TokenizerError(_) => "tokenizer error",
            SyntaxErrorReason::ExpectedFound { .. } => "invalid syntax",

            SyntaxErrorReason::Custom { ref label, .. }
            | SyntaxErrorReason::CustomLabeled { ref label, .. } => label,
        }
    }
}

#[derive(Debug)]
pub struct SyntaxError(Box<SyntaxErrorReason>);

impl Spanned for SyntaxError {
    fn span(&self) -> Span {
        match *self.0 {
            SyntaxErrorReason::TokenizerError(ref err) => err.span(),
            SyntaxErrorReason::ExpectedFound { span, .. }
            | SyntaxErrorReason::Custom { span, .. }
            | SyntaxErrorReason::CustomLabeled { span, .. } => span,
        }
    }
}

impl From<TokenizerError> for SyntaxErrorReason {
    fn from(value: TokenizerError) -> Self {
        SyntaxErrorReason::TokenizerError(value)
    }
}

impl<T: Into<SyntaxErrorReason>> From<T> for SyntaxError {
    fn from(value: T) -> Self {
        SyntaxError(Box::new(value.into()))
    }
}

impl<'src, I: InputTape<'src>> ParserErrorInner<'src, I> for SyntaxError {
    fn custom(span: I::Span, label: impl Into<Cow<'static, str>>, message: impl ToString) -> Self {
        Self(Box::new(SyntaxErrorReason::Custom {
            span,
            label: label.into(),
            message: message.to_string(),
        }))
    }

    fn custom_with_labels(
        span: I::Span,
        label: impl Into<Cow<'static, str>>,
        labels: impl Iterator<Item = (I::Span, impl ToString)>,
    ) -> Self {
        Self(Box::new(SyntaxErrorReason::CustomLabeled {
            span,
            label: label.into(),
            labels: labels.map(|(span, str)| (span, str.to_string())).collect(),
        }))
    }

    fn expected_found<L: Into<Pattern>, It: IntoIterator<Item = L>>(
        expected: It,
        found: Option<TokenKind>,
        span: I::Span,
    ) -> Self {
        SyntaxError(Box::new(SyntaxErrorReason::ExpectedFound {
            expected: expected.into_iter().map(Into::into).collect(),
            found,
            span,
        }))
    }

    fn merge_expected_found<L: Into<Pattern>, It: IntoIterator<Item = L>>(
        mut self,
        new_expected: It,
        new_found: Option<TokenKind>,
        new_span: I::Span,
    ) -> Self {
        if let SyntaxErrorReason::ExpectedFound {
            expected,
            found,
            span,
        } = &mut *self.0
        {
            *span = new_span;
            *found = found.take().or(new_found);
            expected.extend(new_expected.into_iter().map(Into::into));
        }

        self
    }

    fn merge(mut self, other: Self) -> Self {
        let reason = match (*self.0, *other.0) {
            (
                SyntaxErrorReason::ExpectedFound {
                    mut expected,
                    found,
                    span,
                },
                SyntaxErrorReason::ExpectedFound {
                    expected: other_expected,
                    ..
                },
            ) => {
                expected.extend(other_expected);
                SyntaxErrorReason::ExpectedFound {
                    expected,
                    found,
                    span,
                }
            }
            (reason, _) => reason,
        };
        *self.0 = reason;

        self
    }
}

struct InnerError {
    errors: Vec<SyntaxError>,
    contains_fatal_error: bool,
}

#[repr(transparent)]
pub struct ParseErrors(Box<InnerError>);

impl Debug for ParseErrors {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("ParserError").finish_non_exhaustive()
    }
}

impl ParseErrors {
    /// `fatal_errors` stop semantic analysis
    /// `recoverable_errors` don't stop semantic analysis but do stop further compilation
    ///
    /// returns None if there are no errors
    /// and returns some if any iterator yields an error
    pub(crate) fn new(
        fatal_errors: impl IntoIterator<Item = SyntaxError>,
        recoverable_errors: impl IntoIterator<Item = SyntaxError>,
    ) -> Option<Self> {
        let mut contains_fatal_error = false;
        let errors = fatal_errors
            .into_iter()
            .inspect(|_| contains_fatal_error = true)
            .chain(recoverable_errors)
            .collect::<Vec<_>>();

        if errors.is_empty() {
            return None;
        }

        Some(Self(Box::new(InnerError {
            errors,
            contains_fatal_error,
        })))
    }

    pub(crate) fn has_fatal_errors(&self) -> bool {
        self.0.contains_fatal_error
    }
}

/// FIXME this should be revised
impl ParseErrors {
    pub fn reports(&self) -> impl Iterator<Item = Report<'_, Span>> {
        self.0.errors.iter().map(|err| {
            let span = err.span();
            let mut builder = Report::build(ReportKind::Error, span).with_message(err.0.label());

            builder = match &*err.0 {
                SyntaxErrorReason::CustomLabeled { labels, .. } => {
                    let labels = labels
                        .iter()
                        .map(|&(span, ref msg)| Label::new(span).with_message(msg));

                    builder.with_labels(labels)
                }
                _ => builder.with_label(Label::new(span).with_message(&*err.0)),
            };

            builder.finish()
        })
    }
}

// FIXME trait alias

pub trait InputTape<'src>:
    chumsky::input::ValueInput<'src, Span = Span, Token = TokenKind>
{
}

impl<'src, I: chumsky::input::ValueInput<'src, Span = Span, Token = TokenKind>> InputTape<'src>
    for I
{
}

pub trait ParserErrorInner<'src, I: InputTape<'src>> {
    fn custom(span: I::Span, label: impl Into<Cow<'static, str>>, message: impl ToString) -> Self;

    fn custom_with_labels(
        span: I::Span,
        label: impl Into<Cow<'static, str>>,
        labels: impl Iterator<Item = (I::Span, impl ToString)>,
    ) -> Self;

    fn expected_found<L: Into<Pattern>, It: IntoIterator<Item = L>>(
        expected: It,
        found: Option<TokenKind>,
        span: I::Span,
    ) -> Self;

    fn merge_expected_found<L: Into<Pattern>, It: IntoIterator<Item = L>>(
        self,
        expected: It,
        found: Option<TokenKind>,
        span: I::Span,
    ) -> Self;

    fn merge(self, other: Self) -> Self;
}

pub struct ParserErrorWrapper<E>(pub E);

impl<'src, I: InputTape<'src>, E: ParserErrorInner<'src, I>, L: Into<Pattern>>
    LabelError<'src, I, L> for ParserErrorWrapper<E>
{
    fn expected_found<It: IntoIterator<Item = L>>(
        expected: It,
        found: Option<MaybeRef<'src, I::Token>>,
        span: I::Span,
    ) -> Self {
        ParserErrorWrapper(E::expected_found(
            expected,
            found.map(MaybeRef::into_inner),
            span,
        ))
    }

    fn merge_expected_found<It: IntoIterator<Item = L>>(
        self,
        expected: It,
        found: Option<MaybeRef<'src, I::Token>>,
        span: I::Span,
    ) -> Self {
        ParserErrorWrapper(E::merge_expected_found(
            self.0,
            expected,
            found.map(MaybeRef::into_inner),
            span,
        ))
    }
}

impl<'src, I: InputTape<'src>, E: ParserErrorInner<'src, I>> chumsky::error::Error<'src, I>
    for ParserErrorWrapper<E>
{
    fn merge(self, other: Self) -> Self {
        ParserErrorWrapper(E::merge(self.0, other.0))
    }
}

pub trait ParserError<'src, I: InputTape<'src>>:
    chumsky::error::Error<'src, I> + LabelError<'src, I, Pattern>
{
    fn custom(span: I::Span, label: impl Into<Cow<'static, str>>, message: impl ToString) -> Self;

    fn custom_with_labels(
        span: I::Span,
        label: impl Into<Cow<'static, str>>,
        labels: impl IntoIterator<Item = (I::Span, impl ToString)>,
    ) -> Self;
}

impl<'src, I: InputTape<'src>, E: ParserErrorInner<'src, I>> ParserError<'src, I>
    for ParserErrorWrapper<E>
{
    fn custom(span: I::Span, label: impl Into<Cow<'static, str>>, message: impl ToString) -> Self {
        ParserErrorWrapper(E::custom(span, label, message))
    }

    fn custom_with_labels(
        span: I::Span,
        label: impl Into<Cow<'static, str>>,
        labels: impl IntoIterator<Item = (I::Span, impl ToString)>,
    ) -> Self {
        ParserErrorWrapper(E::custom_with_labels(span, label, labels.into_iter()))
    }
}

pub struct ParserState<'src, E> {
    pub interner: &'src mut Interner,
    pub text: &'src str,
    /// errors in the rules of the syntax
    /// but not the actual syntax
    /// a prime example is chaining comparison operators
    pub produced_errors: Vec<E>,
}

pub trait ParserData<'src, I: InputTape<'src>>:
    chumsky::extra::ParserExtra<
        'src,
        I,
        Error: ParserError<'src, I>,
        State = SimpleState<
            ParserState<'src, <Self as chumsky::extra::ParserExtra<'src, I>>::Error>,
        >,
    > + 'src
{
}

impl<'src, I: InputTape<'src>, PE> ParserData<'src, I> for PE where
    PE: chumsky::extra::ParserExtra<
            'src,
            I,
            Error: ParserError<'src, I>,
            State = SimpleState<
                ParserState<'src, <Self as chumsky::extra::ParserExtra<'src, I>>::Error>,
            >,
        > + 'src
{
}

pub trait OvalParser<'src, I: InputTape<'src>, O, E: ParserData<'src, I>>:
    chumsky::Parser<'src, I, O, E> + Copy + Send + Sync
{
}

impl<
    'src,
    I: InputTape<'src>,
    O,
    E: ParserData<'src, I>,
    P: chumsky::Parser<'src, I, O, E> + Copy + Send + Sync,
> OvalParser<'src, I, O, E> for P
{
}

pub(crate) trait AstParse: Sized {
    fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>()
    -> impl OvalParser<'src, I, Self, E>;
}
