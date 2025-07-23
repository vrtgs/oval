use crate::compile::syntax::block::expr::Expr;
use crate::compile::syntax::item::Item;
use crate::compile::syntax::r#type::Type;
use crate::compile::syntax::{
    OvalParserExt, Parser, ParserExtra, Pattern, SealedParseAst, recursive_parser,
};
use crate::compile::tokenizer::Token;
use alloc::vec;
use alloc::vec::Vec;
use chumsky::input::Input;
use chumsky::prelude::SimpleSpan;

pub mod expr;

#[derive(Debug, Clone)]
pub struct Local {
    pub let_span: SimpleSpan,
    pub mut_span: Option<SimpleSpan>,
    pub binding: Pattern,
    pub ty: Type,
    pub init: Option<Expr>,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Declaration(Local),
    Item(Item),
    // the span is for the optional semicolon
    Expr { expr: Expr, terminated: bool },
}

impl SealedParseAst for Statement {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        chumsky::primitive::todo()
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub statements: Vec<Statement>,
}

impl SealedParseAst for Block {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        let expr_parser = recursive_parser::<Expr, I>();
        expr_parser.in_curly_brackets().map(|expr| Self {
            statements: vec![Statement::Expr {
                expr,
                terminated: false,
            }],
        })
    }
}
