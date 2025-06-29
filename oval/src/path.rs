use alloc::string::String;
use alloc::vec::Vec;
use alloc::vec;
use core::fmt::{Debug, Display, Formatter};
use core::str::FromStr;
use thiserror::Error;
use cow_array::MinSizedCowArray;
use crate::compile::tokenizer::{tokenize, TokenKind};

#[derive(Debug, Error)]
pub enum FromStrError {
    #[error("item can't be empty")]
    Empty,
    #[error("unexpected token; expected {expected:?}, found {found:?}")]
    UnexpectedToken {
        expected: Vec<Option<TokenKind>>,
        found: TokenKind,
    }
}

fn unexpected_token(expected: Option<TokenKind>, found: TokenKind) -> FromStrError {
    FromStrError::UnexpectedToken {
        expected: vec![expected],
        found
    }
}

#[derive(Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub struct Ident(MinSizedCowArray<u8, 1>);

impl FromStr for Ident {
    type Err = FromStrError;
    
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut tokens = tokenize(s);
        let err = |expected, token| Err(unexpected_token(expected, token));
        match tokens.next().map(|tk| (tk.kind(), tk.span())) {
            Some((TokenKind::Ident, span)) => {
               match tokens.next() {
                   None => {
                       let ident = &s[span.into_range()];
                       let token = MinSizedCowArray::copy_from_slice(ident.as_bytes())
                           .expect("ident should not be empty");
                       Ok(Self(token))
                   }
                   Some(token) => err(None, token.kind()),
               }
            }
            Some((token, _)) => err(Some(TokenKind::Ident), token),
            None => Err(Self::Err::Empty),
        }
    }
}

impl Ident {
    pub fn as_str(&self) -> &str {
        str::from_utf8(&self.0).unwrap()
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        Display::fmt(self.as_str(), f)
    }
}

impl Debug for Ident {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        Display::fmt(self, f)
    }
}

#[derive(Clone, Debug, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub struct Path(MinSizedCowArray<Ident, 1>);

impl FromStr for Path {
    type Err = FromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut victor = vec![];
        for (i, token) in tokenize(s).enumerate() {
            match i % 2 {
                0 => {
                    if token.kind() != TokenKind::Ident {
                        return Err(FromStrError::UnexpectedToken {
                            expected: vec![Some(TokenKind::Ident)],
                            found: token.kind()
                        })
                    }
                    victor.push({
                        let bytes = MinSizedCowArray::copy_from_slice(s[token.span().into_range()].as_bytes())
                            .unwrap();
                        Ident(bytes)
                    })
                },
                1 => {
                    if token.kind() != TokenKind::DoubleColon {
                        return Err(FromStrError::UnexpectedToken {
                            expected: vec![
                                Some(TokenKind::DoubleColon),
                                None
                            ],
                            found: token.kind()
                        })
                    }
                },
                _ => unreachable!()
            }
        }

        MinSizedCowArray::from_vec(victor)
            .map_err(|_| FromStrError::Empty)
            .map(Self)
    }
}

impl Display for Path {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let [first] = self.0.head();
        let first = first.as_str();
        
        let tail = self.0.tail();
        if tail.is_empty() { 
            return Display::fmt(first, f);
        }
        
        let mut str = String::with_capacity(tail.iter().fold(
            first.len(),
            |value, next| value + 2 + next.as_str().len()
        ));

        str.push_str(first);
        for item in tail {
            str.push_str("::");
            str.push_str(item.as_str())
        }
        
        Display::fmt(str.as_str(), f)
    }
    
}