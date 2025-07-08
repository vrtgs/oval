use alloc::vec::Vec;
use alloc::vec;
use crate::compile::parser::block::Block;
use crate::compile::parser::{AllowTrailing, ParseAst, Parser};
use crate::compile::parser::r#type::Type;
use crate::compile::span::SimpleSpan;
use crate::symbol::Ident;
use crate::compile::error::{Error, Result};
use crate::compile::parser::block::expr::Expr;
use crate::compile::tokenizer::{TokenKind, TokenTreeKind};


#[derive(Debug)]
enum Visibility {
    Public,
    Private,
}

impl ParseAst for Visibility {
    fn parse_inner<'src>(parser: &mut Parser<'src, '_, '_>) -> Result<'src, Self> {
        Ok(parser.maybe_eat(TokenKind::Pub).map_or(Visibility::Private, |_| Visibility::Public))
    }
}

#[derive(Debug)]
pub struct Function {
    visibility: Visibility,
    name: Ident,
    arguments: Vec<(Ident, Type)>,
    return_type: Type,
    body: Block
}

impl ParseAst for Function {
    fn parse_inner<'src>(parser: &mut Parser<'src, '_, '_>) -> Result<'src, Self> {
        let visibility = parser.parse::<Visibility>()?;

        parser.eat(TokenKind::Fn)?;
        let name = parser.parse::<Ident>()?;
        let TokenTreeKind::Paren(sub_slice) = parser.eat(TokenKind::RParen)?.kind() else {
            unreachable!()
        };

        let args = {
            let mut arg_parser = parser.sub_parser(sub_slice);
            arg_parser.parse_list_with::<(Ident, Type), AllowTrailing>(TokenKind::Comma, |parser| {
                let ident = Ident::parse_inner(parser)?;
                let _colon = parser.eat(TokenKind::Colon)?;
                let ty = Type::parse_inner(parser)?;
                Ok((ident, ty))
            })?
        };


        
        let ty = match parser.maybe_eat(TokenKind::Arrow) {
            Some(_) => parser.parse::<Type>()?,
            None => Type::Tuple(vec![])
        };

        let body = parser.parse::<Block>()?;

        Ok(Self {
            visibility,
            name,
            arguments: args,
            return_type: ty,
            body,
        })
    }
}


#[derive(Debug)]
pub struct ConstItem {
    visibility: Visibility,
    name: Ident,
    ty: Type,
    val: Expr
}

impl ParseAst for ConstItem {
    fn parse_inner<'src>(parser: &mut Parser<'src, '_, '_>) -> Result<'src, Self> {
        let visibility = parser.parse::<Visibility>()?;
        
        parser.eat(TokenKind::Const)?;
        let name = parser.parse::<Ident>()?;
        parser.eat(TokenKind::Colon)?;
        let ty = parser.parse::<Type>()?;
        parser.eat(TokenKind::Assign)?;
        let val = parser.parse::<Expr>()?;
        parser.eat(TokenKind::SemiColon)?;
        
        Ok(Self {
            visibility,
            name,
            ty,
            val,
        })
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum ItemRepr {
    Function(Function),
    Const(ConstItem)
}

#[derive(Debug)]
pub struct Item {
    span: SimpleSpan,
    repr: ItemRepr
}

impl ParseAst for Item {
    fn parse_inner<'src>(parser: &mut Parser<'src, '_, '_>) -> Result<'src, Self> {
        let mut errors = vec![];
        macro_rules! try_parse {
            ($($path:ident($T: ty)),+ $(,)?) => {
                $(match parser.parse_spanned::<$T>() {
                    Ok((item, span)) => return Ok(Self {
                        span: span.expect("items can't be empty"),
                        repr: ItemRepr::$path(item)
                    }),
                    Err(err) => errors.push(err)
                })+
            };
        }


        try_parse!(
            Function(Function),
            Const(ConstItem),
        );


        Err(errors.into_iter().reduce(Error::merge).expect("at at least one error occurred"))
    }
}