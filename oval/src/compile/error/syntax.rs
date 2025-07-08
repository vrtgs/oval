use alloc::borrow::Cow;
use core::fmt::{Debug, Display, Formatter};
use core::error::Error;
use alloc::vec::Vec;
use core::cmp::Ordering;
use thiserror::Error;
use crate::compile::span::SimpleSpan;
use crate::compile::tokenizer::{TokenKind, TokenTree};

#[derive(Copy, Clone, Eq, PartialEq)]
struct DisplayToken(Option<TokenKind>);

impl PartialOrd for DisplayToken {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DisplayToken {
    fn cmp(&self, other: &Self) -> Ordering {
        let map = |opt: &Self| (opt.0.is_none(), opt.0);
        Ord::cmp(&map(self), &map(other))
    }
}

impl Display for DisplayToken {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.0 {
            None => f.write_str("<EOF>"),
            Some(token) => f.write_str(token.repr()),
        }
    }
}

impl Debug for DisplayToken {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        Display::fmt(self, f)
    }
}

#[derive(Debug, Error)]
struct UnexpectedTokenError {
    expected: Vec<DisplayToken>,
    found: DisplayToken
}

impl Display for UnexpectedTokenError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let Self { expected, found } = self;
        match &**expected {
            [] => write!(f, "unexpected token {found}"),
            [expected] => write!(f, "unexpected token; expected {expected}, found {found}"),
            expected => write!(f, "unexpected token; expected one of {expected:?}, found {found}")
        }
    }
}

impl UnexpectedTokenError {
    #[cold]
    #[inline(never)]
    pub fn new(expected: Vec<DisplayToken>, found: DisplayToken) -> UnexpectedTokenError {
        let mut expected = expected;
        
        // sort by Some(token) then None, and sort tokens in arbitrary but consistent order
        expected.sort_unstable();
        // already sorted
        expected.dedup();
        
        debug_assert!(
            !expected.contains(&found),
            "expected token was found, but compiler reported an error"
        );
        
        UnexpectedTokenError {
            expected,
            found,
        }
    }
}


#[derive(Debug, Error)]
#[error("{0}")]
struct CustomError(Cow<'static, str>);

#[derive(Debug)]
enum SyntaxErrorInner {
    UnexpectedToken(UnexpectedTokenError),
    Custom(CustomError),
}

#[derive(Debug)]
pub struct SyntaxError {
    span: Option<SimpleSpan>,
    inner: SyntaxErrorInner
}

pub trait Found {
    fn found(self) -> Option<(SimpleSpan, TokenKind)>;
}

trait FoundOk {
    fn found_ok(self) -> (SimpleSpan, TokenKind);
}

impl<F: FoundOk> Found for F {
    fn found(self) -> Option<(SimpleSpan, TokenKind)> {
        Some(self.found_ok())
    }
}

impl FoundOk for (SimpleSpan, TokenKind) {
    fn found_ok(self) -> (SimpleSpan, TokenKind) {
        self
    }
}

impl FoundOk for &TokenTree {
    fn found_ok(self) -> (SimpleSpan, TokenKind) {
        (self.span(), self.start_token_kind())
    }
}

impl<F: FoundOk> Found for Option<F> {
    fn found(self) -> Option<(SimpleSpan, TokenKind)> {
        self.map(|f| f.found_ok())
    }
}

pub struct Eos;

impl Found for Eos {
    fn found(self) -> Option<(SimpleSpan, TokenKind)> {
        None
    }
}

impl SyntaxError {
    pub fn expected_found(expected: impl Iterator<Item=impl Into<Option<TokenKind>>>, found: impl Found) -> Self {
        let expected = expected
            .into_iter()
            .map(Into::into)
            .map(DisplayToken)
            .collect::<Vec<_>>();

        let (span, found) = found.found()
            .map_or((None, None), |(span, tt)| (Some(span) , Some(tt)));

        let found = DisplayToken(found);
        SyntaxError {
            span,
            inner: SyntaxErrorInner::UnexpectedToken(UnexpectedTokenError::new(
                expected,
                found
            ))
        }
    }

    pub fn unexpected_token(found: impl Found) -> Self {
        enum Void {}

        impl From<Void> for Option<TokenKind> {
            fn from(value: Void) -> Self {
                match value {}
            }
        }
        
        Self::expected_found(<[Void; 0]>::into_iter([]), found)
    }

    pub fn custom(span: impl Into<Option<SimpleSpan>>, message: impl Into<Cow<'static, str>>) -> Self {
        SyntaxError {
            span: span.into(),
            inner: SyntaxErrorInner::Custom(CustomError(message.into()))
        }
    }

    pub fn span(&self) -> Option<SimpleSpan> {
        self.span
    }

    fn inner(&self) -> &(dyn Error + 'static) {
        match &self.inner {
            SyntaxErrorInner::UnexpectedToken(tk) => tk,
            SyntaxErrorInner::Custom(cus) => cus
        }
    }
}

impl Display for SyntaxError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self.span().map(|span| span.into_range()) {
            Some(span) => write!(f, "unexpected syntax error at [{span:?}]: {}", self.inner()),
            None => write!(f, "unexpected syntax error: {}", self.inner())
        }
    }
}

impl Error for SyntaxError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(self.inner())
    }
}