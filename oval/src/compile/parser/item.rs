use chumsky::IterParser;
use alloc::vec::Vec;
use alloc::vec;
use chumsky::input::ValueInput;
use chumsky::Parser;
use chumsky::prelude::{just, SimpleSpan};
use crate::compile::parser::block::Block;
use crate::compile::parser::r#type::Type;
use crate::symbol::Ident;
use crate::compile::parser::block::expr::Expr;
use crate::compile::parser::{make_recursive_parsers, OvalParserExt, SealedParseAst, ParserExtra};
use crate::compile::tokenizer::Token;


#[derive(Debug, Copy, Clone)]
pub enum Visibility {
    Public,
    Private,
}

impl SealedParseAst for Visibility {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        just(Token::Pub).or_not().map(|tok| match tok {
            Some(_) => Visibility::Public,
            None => Visibility::Private
        })
    }
}

#[derive(Debug, Clone)]
pub struct FunctionItem {
    pub visibility: Visibility,
    pub name: Ident,
    pub arguments: Vec<(Ident, Type)>,
    pub return_type: Type,
    pub body: Block
}

impl FunctionItem {
    pub(super) fn make_parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>(
        block: impl Parser<'a, I, Block, ParserExtra<'a>> + Clone
    ) -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        let arg_parser = Ident::parser()
            .then_ignore(just(Token::Colon))
            .then(Type::parser())
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>()
            .in_parens();

        let return_type_parser = just(Token::Arrow)
            .ignore_then(Type::parser())
            .or_not()
            .map(|x| x.unwrap_or(const { Type::Tuple(vec![]) }));

        Visibility::parser()
            .then_ignore(just(Token::Fn))
            .then(Ident::parser())
            .then(arg_parser)
            .then(return_type_parser)
            .then(block)
            .map(|((((visibility, name), arguments), return_type), body)| {
                FunctionItem {
                    visibility,
                    name,
                    arguments,
                    return_type,
                    body,
                }
            })
    }
}

impl SealedParseAst for FunctionItem {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        make_recursive_parsers().2
    }
}


#[derive(Debug, Clone)]
pub struct ConstItem {
    pub visibility: Visibility,
    pub name: Ident,
    pub ty: Type,
    pub value: Expr
}

impl ConstItem {
    pub(super) fn make_parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>(
        expr: impl Parser<'a, I, Expr, ParserExtra<'a>> + Clone
    ) -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        Visibility::parser()
            .then_ignore(just(Token::Const))
            .then(Ident::parser())
            .then_ignore(just(Token::Colon))
            .then(Type::parser())
            .then_ignore(just(Token::Assign))
            .then(expr)
            .then_ignore(just(Token::SemiColon))
            .map(|(((visibility, name), ty), value)| {
                ConstItem {
                    visibility,
                    name,
                    ty,
                    value,
                }
            })
    }
}

impl SealedParseAst for ConstItem {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        make_recursive_parsers().3
    }
}

#[derive(Debug, Clone)]
pub enum Item {
    Function(FunctionItem),
    Const(ConstItem)
}

impl SealedParseAst for Item {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        make_recursive_parsers().4
    }
}