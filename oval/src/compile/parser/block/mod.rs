use alloc::vec::Vec;
use alloc::vec;
use chumsky::input::ValueInput;
use chumsky::prelude::SimpleSpan;
use crate::compile::parser::{make_recursive_parsers, OvalParserExt, SealedParseAst, Parser, ParserExtra};
use crate::compile::parser::block::expr::Expr;
use crate::compile::parser::item::Item;
use crate::compile::parser::r#type::Type;
use crate::compile::tokenizer::Token;
use crate::symbol::{Ident};


pub mod expr;


#[derive(Debug, Clone)]
pub struct Local {
    pub let_span: SimpleSpan,
    pub mut_span: Option<SimpleSpan>,
    pub name: Ident,
    pub ty: Type,
    pub init: Option<Expr>
}

#[derive(Debug, Clone)]
pub enum Statement {
    Declaration(Local),
    Item(Item),
    // the span is for the optional semicolon
    Expr { expr: Expr, terminated: bool }
}

impl SealedParseAst for Statement {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        chumsky::primitive::todo()
    }
}


#[derive(Debug, Clone)]
pub struct Block {
    pub statements: Vec<Statement>,
}

impl Block {
    pub(crate) fn make_parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>(
        expr_parser: impl Parser<'a, I, Expr, ParserExtra<'a>> + Clone,
        _item_parser: impl Parser<'a, I, Item, ParserExtra<'a>> + Clone,
    ) -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        expr_parser.in_curly_brackets().map(|expr| {
            Self {
                statements: vec![Statement::Expr { expr, terminated: false }],
            }
        })
    }
}


impl SealedParseAst for Block {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        make_recursive_parsers().1
    }
}