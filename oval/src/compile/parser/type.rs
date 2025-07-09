use alloc::boxed::Box;
use alloc::vec::Vec;
use chumsky::input::ValueInput;
use chumsky::{IterParser, Parser};
use chumsky::prelude::{just, SimpleSpan};
use chumsky::primitive::choice;
use chumsky::recursive::recursive;
use crate::compile::parser::{OvalParserExt, SealedParseAst, ParserExtra};
use crate::compile::tokenizer::Token;
use crate::symbol::Path;



#[derive(Debug, Clone)]
pub enum Type {
    Tuple(Vec<Type>),
    Parens(Box<Type>),
    Array(Box<Type>),
    Path(Path),
    Infer,
}

impl SealedParseAst for Type {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        recursive(|type_parser| {
            let tuple_parser = type_parser
                .clone()
                .separated_by(just(Token::Comma))
                .collect::<Vec<Type>>()
                .then(just(Token::Comma).or_not().map(|tok| tok.is_some()))
                .in_parens()
                // TODO: tuple parsing with less code duplication
                .map(|(mut types, leading)| {
                    if !leading {
                        match <[_; 1]>::try_from(types) {
                            Ok([x]) => return Type::Parens(Box::new(x)),
                            Err(fail) => types = fail
                        }
                    }

                    Type::Tuple(types)
                });

            let array_parser = type_parser
                .in_square_brackets()
                .map(|ty| Type::Array(Box::new(ty)));

            choice((
                just(Token::Wildcard).map(|_| Type::Infer),
                Path::parser().map(Type::Path),
                tuple_parser,
                array_parser
            ))
        })
    }
}