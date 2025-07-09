use alloc::vec::Vec;
use alloc::vec;
use chumsky::input::ValueInput;
use chumsky::prelude::SimpleSpan;
use crate::compile::parser::{recursive_parsers, OvalParserExt, ParseAst, Parser, ParserExtra};
use crate::compile::parser::block::expr::Expr;
use crate::compile::parser::item::Item;
use crate::compile::parser::r#type::Type;
use crate::compile::tokenizer::Token;
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
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        chumsky::primitive::todo()
    }
}


#[derive(Debug)]
pub struct Block {
    statements: Vec<Statement>,
    span: SimpleSpan,
}

impl Block {
    pub(crate) fn make_parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>(
        expr_parser: impl Parser<'a, I, Expr, ParserExtra<'a>> + Clone,
    ) -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        expr_parser.in_curly_brackets().map_with(|expr, extra| {
            Self {
                statements: vec![Statement::Expr { expr, terminated: false }],
                span: extra.span(),
            }
        })
    }
}


impl ParseAst for Block {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        recursive_parsers().block
    }
}