use alloc::boxed::Box;
use alloc::vec::Vec;
use crate::compile::parser::{Tuple, ParseAst, Parser, TupleOrParens};
use crate::compile::tokenizer::{TokenKind, TokenTreeKind};
use crate::symbol::Path;



#[derive(Debug)]
pub enum Type {
    Tuple(Vec<Type>),
    Array(Box<Type>),
    Parens(Box<Type>),
    Path(Path),
    Infer,
}

impl ParseAst for Type {
    fn parse_inner<'src>(parser: &mut Parser<'src, '_, '_>) -> crate::compile::error::Result<'src, Self> {
        if let Ok(path) = parser.parse::<Path>() {
            return Ok(Type::Path(path))
        }

        parser.eat_with(|tt, parser| {
            Ok(Some(match tt.kind() {
                TokenTreeKind::Wildcard => Type::Infer,
                TokenTreeKind::Paren(tt) => {
                    let mut parens = parser.sub_parser(tt);
                    let res = parens.parse_list::<Type, Tuple>(TokenKind::Comma)?;
                    match res {
                        TupleOrParens::Parens(t) => Type::Parens(Box::new(t)),
                        TupleOrParens::Tuple(ts) => Type::Tuple(ts),
                    }
                },
                TokenTreeKind::Bracket(tt) => {
                    let ty = parser.sub_parser(tt).parse::<Self>()?;
                    parser.assert_eos()?;
                    Self::Parens(Box::new(ty))
                }
                _ => return Ok(None)
            }))
        })
    }
}