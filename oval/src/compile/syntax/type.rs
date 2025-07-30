use crate::compile::syntax::{OvalParserExt, ParserExtra, SealedParseAst, recursive_parser};
use crate::compile::tokenizer::Token;
use crate::symbol::Path;
use alloc::boxed::Box;
use alloc::vec::Vec;
use chumsky::Parser;
use chumsky::input::Input;
use chumsky::prelude::{SimpleSpan, just};
use chumsky::primitive::choice;

#[derive(Debug, Clone)]
pub enum Type {
    Tuple(Vec<Type>),
    Parens(Box<Type>),
    Array(Box<Type>),
    Path(Path),
    Infer,
}

impl SealedParseAst for Type {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Copy {
        let type_parser = recursive_parser::<Self, I>();

        let tuple_parser = type_parser.box_or_tuple(Type::Parens, Type::Tuple);

        let array_parser = type_parser
            .in_square_brackets()
            .map(|ty| Type::Array(Box::new(ty)));

        choice((
            just(Token::Wildcard).map(|_| Type::Infer),
            Path::parser().map(Type::Path),
            tuple_parser,
            array_parser,
        ))
    }
}
