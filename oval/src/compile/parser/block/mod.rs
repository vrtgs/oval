use alloc::vec::Vec;
use alloc::vec;
use crate::compile::parser::{Item, ParseAst, Parser};
use crate::compile::parser::block::expr::Expr;
use crate::compile::parser::r#type::Type;
use crate::compile::span::SimpleSpan;
use crate::compile::tokenizer::{TokenKind, TokenTreeKind};
use crate::symbol::{Ident};


pub mod expr;


#[derive(Debug)]
pub struct Local {
    let_span: SimpleSpan,
    mut_span: Option<SimpleSpan>,
    name: Ident,
    ty: Type
}

#[derive(Debug)]
pub enum Statement {
    Declaration(Local),
    Item(Item),
    // the span is for the optional semicolon
    Expr { expr: Expr, terminated: bool }
}

impl ParseAst for Statement {
    fn parse_inner<'src>(_: &mut Parser<'src, '_, '_>) -> crate::compile::error::Result<'src, Self> {
        todo!()
    }
}


#[derive(Debug)]
pub struct Block {
    statements: Vec<Statement>,
    span: SimpleSpan,
}


impl ParseAst for Block {
    fn parse_inner<'src>(parser: &mut Parser<'src, '_, '_>) -> crate::compile::error::Result<'src, Self> {
        let TokenTreeKind::Bracket(bracket) = parser.eat(TokenKind::RBracket)?.kind() else {
            unreachable!()
        };

        let mut parser = parser.sub_parser(bracket);
        let expr = parser.parse::<Expr>()?;
        parser.assert_eos()?;
        Ok(Self {
            statements: vec![Statement::Expr { expr, terminated: false }],
            span: SimpleSpan::EMPTY,
        })
    }
}