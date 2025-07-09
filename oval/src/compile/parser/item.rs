use chumsky::IterParser;
use alloc::vec::Vec;
use alloc::vec;
use chumsky::input::ValueInput;
use chumsky::Parser;
use chumsky::prelude::{choice, just, SimpleSpan};
use crate::compile::parser::block::Block;
use crate::compile::parser::r#type::Type;
use crate::symbol::Ident;
use crate::compile::parser::block::expr::Expr;
use crate::compile::parser::{OvalParserExt, ParseAst, ParserExtra};
use crate::compile::tokenizer::Token;


#[derive(Debug)]
enum Visibility {
    Public,
    Private,
}

impl ParseAst for Visibility {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        just(Token::Pub).or_not().map(|tok| match tok {
            Some(_) => Visibility::Public,
            None => Visibility::Private
        })
    }
}

#[derive(Debug)]
pub struct FunctionItem {
    visibility: Visibility,
    name: Ident,
    arguments: Vec<(Ident, Type)>,
    return_type: Type,
    body: Block
}

impl ParseAst for FunctionItem {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
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
            .then(Block::parser())
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


#[derive(Debug)]
pub struct ConstItem {
    visibility: Visibility,
    name: Ident,
    ty: Type,
    value: Expr
}

impl ParseAst for ConstItem {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        Visibility::parser()
            .then_ignore(just(Token::Const))
            .then(Ident::parser())
            .then_ignore(just(Token::Colon))
            .then(Type::parser())
            .then_ignore(just(Token::Assign))
            .then(Expr::parser())
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

#[derive(Debug)]
#[non_exhaustive]
pub enum ItemRepr {
    Function(FunctionItem),
    Const(ConstItem)
}

#[derive(Debug)]
pub struct Item {
    span: SimpleSpan,
    repr: ItemRepr
}

impl ParseAst for Item {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        choice((
            FunctionItem::parser().map(ItemRepr::Function),
            ConstItem::parser().map(ItemRepr::Const)
        )).map_with(|repr, extra| Item {
            span: extra.span(),
            repr
        })
    }
}