use crate::compile::syntax::block::Block;
use crate::compile::syntax::block::expr::Expr;
use crate::compile::syntax::r#type::Type;
use crate::compile::syntax::{
    OvalParserExt, ParserExtra, Pattern, SealedParseAst, make_recursive_parsers,
};
use crate::compile::tokenizer::Token;
use crate::symbol::{Ident, Path};
use alloc::vec;
use alloc::vec::Vec;
use chumsky::IterParser;
use chumsky::Parser;
use chumsky::input::Input;
use chumsky::prelude::{SimpleSpan, just};

#[derive(Debug, Copy, Clone)]
pub enum Visibility {
    Public,
    Private,
}

impl SealedParseAst for Visibility {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        just(Token::Pub).or_not().map(|tok| match tok {
            Some(_) => Visibility::Public,
            None => Visibility::Private,
        })
    }
}

#[derive(Debug, Clone)]
pub struct FunctionItem {
    pub visibility: Visibility,
    pub name: Ident,
    pub arguments: Vec<(Pattern, Type)>,
    pub return_type: Type,
    pub body: Block,
}

impl FunctionItem {
    pub(super) fn make_parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>(
        block: impl Parser<'a, I, Block, ParserExtra<'a>> + Clone,
    ) -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        let arg_parser = Pattern::parser()
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
            .map(
                |((((visibility, name), arguments), return_type), body)| FunctionItem {
                    visibility,
                    name,
                    arguments,
                    return_type,
                    body,
                },
            )
    }
}

impl SealedParseAst for FunctionItem {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        make_recursive_parsers().2
    }
}

#[derive(Debug, Clone)]
pub struct ConstItem {
    pub visibility: Visibility,
    pub binding: Pattern,
    pub ty: Type,
    pub value: Expr,
}

impl ConstItem {
    pub(super) fn make_parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>(
        expr: impl Parser<'a, I, Expr, ParserExtra<'a>> + Clone,
    ) -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        Visibility::parser()
            .then_ignore(just(Token::Const))
            .then(Pattern::parser())
            .then_ignore(just(Token::Colon))
            .then(Type::parser())
            .then_ignore(just(Token::Assign))
            .then(expr)
            .then_ignore(just(Token::SemiColon))
            .map(|(((visibility, pattern), ty), value)| ConstItem {
                visibility,
                binding: pattern,
                ty,
                value,
            })
    }
}

impl SealedParseAst for ConstItem {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        make_recursive_parsers().3
    }
}

#[derive(Debug, Clone)]
pub struct UseItem {
    pub visibility: Visibility,
    pub path: Path,
}

impl SealedParseAst for UseItem {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        Visibility::parser()
            .then(just(Token::Use).ignore_then(Path::parser()))
            .then_ignore(just(Token::SemiColon))
            .map(|(vis, path)| UseItem {
                visibility: vis,
                path,
            })
    }
}

#[derive(Debug, Clone)]
pub enum Item {
    Function(FunctionItem),
    Const(ConstItem),
    Use(UseItem),
}

impl Item {
    pub(super) fn make_parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>(
        func_item: impl Parser<'a, I, FunctionItem, ParserExtra<'a>> + Clone,
        const_item: impl Parser<'a, I, ConstItem, ParserExtra<'a>> + Clone,
    ) -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        macro_rules! make_item_parser {
        ($($parser: expr => $ty:ident),+ $(,)?) => {{
            fn _assert_all_parsed() -> () {
                fn get<T>() -> T {
                    todo!()
                }

                let item = get::<Item>();
                #[deny(unreachable_patterns)]
                match item {
                    $(Item::$ty(_) => unreachable!()),+
                }
            }

            chumsky::primitive::choice((
                $(($parser).map(Item::$ty),)+
            ))
        }};
    }

        make_item_parser!(
            func_item => Function,
            const_item => Const,
            UseItem::parser() => Use
        )
    }
}

impl SealedParseAst for Item {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        make_recursive_parsers().4
    }
}
