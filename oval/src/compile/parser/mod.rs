use alloc::vec::Vec;
use chumsky::error::Rich;
use chumsky::extra::SimpleState;
use chumsky::input::ValueInput;
use chumsky::{IterParser, Parser};
use chumsky::combinator::DelimitedBy;
use chumsky::prelude::just;
use chumsky::primitive::Just;
use chumsky::recursive::Recursive;
use chumsky::span::SimpleSpan;
use crate::compile::compiler::Compiler;
use crate::compile::error::Error;
use crate::compile::parser::block::Block;
use crate::compile::parser::block::expr::Expr;
use crate::compile::parser::item::Item;
use crate::compile::source_file::SourceFile;
use crate::compile::Spanned;
use crate::compile::tokenizer::{Token, TokenizedSource};

pub mod block;
pub mod r#type;
pub mod item;

pub(crate) type ParserExtra<'a> = chumsky::extra::Full<Rich<'a, Token, SimpleSpan>, SimpleState<(&'a SourceFile, &'a mut Compiler)>, ()>;

pub(crate) type Delimited<'a, T, I> = DelimitedBy<T, Just<Token, I, ParserExtra<'a>>, Just<Token, I, ParserExtra<'a>>, Token, Token>;

pub(crate) trait OvalParserExt<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>, O>: Parser<'a, I, O, ParserExtra<'a>> + Sized {
    fn in_parens(self) -> Delimited<'a, Self, I> {
        self.delimited_by(just(Token::LParen), just(Token::RParen))
    }

    fn in_square_brackets(self) -> Delimited<'a, Self, I> {
        self.delimited_by(just(Token::LSquareBracket), just(Token::RSquareBracket))
    }

    fn in_curly_brackets(self) -> Delimited<'a, Self, I> {
        self.delimited_by(just(Token::LBracket), just(Token::RBracket))
    }
}

impl<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>, O, P: Parser<'a, I, O, ParserExtra<'a>> + Sized> OvalParserExt <'a, I, O> for P {}

pub(crate) trait ParseAst: Sized + 'static {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone;
}

struct RecursiveParsers<P1, P2> {
    expr: P1,
    block: P2,
}

pub(crate) fn recursive_parsers<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> RecursiveParsers<
    impl Parser<'a, I, Expr, ParserExtra<'a>> + Clone,
    impl Parser<'a, I, Block, ParserExtra<'a>> + Clone,
> {
    let mut block = Recursive::declare();
    let expr = Expr::make_parser(block.clone());
    block.define(Block::make_parser(expr.clone()));

    RecursiveParsers {
        expr,
        block
    }
}

pub(crate) fn parse_from_source<'a, O: ParseAst>(tokenized: TokenizedSource<'a>, compiler: &mut Compiler) -> Result<O, Error<'a>> {
    let source = tokenized.source();
    let contents = source.contents();
    let tokens = chumsky::input::Input::map(
        tokenized.tokens_slice(),
        (contents.len()..contents.len()).into(),
        (|tok: &Spanned<Token>| (&tok.value, &tok.span)) as fn(_) -> _
    );

    let mut state: SimpleState<(&SourceFile, &mut Compiler)> = SimpleState((source, compiler));


    O::parser()
        .parse_with_state(tokens, &mut state)
        .into_result()
        .map_err(|errors| {
            Error::syntax_error(source, errors)
        })
}

#[derive(Debug)]
pub struct OvalFile<'a> {
    file: &'a SourceFile,
    items: Vec<Item>
}

pub fn parse_file<'a>(tokenized: TokenizedSource<'a>, compiler: &mut Compiler) -> Result<OvalFile<'a>, Error<'a>> {
    struct Items(Vec<Item>);


    impl ParseAst for Items {
        fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
            Item::parser().repeated().collect().map(Items)
        }
    }

    let source = tokenized.source();
    parse_from_source::<Items>(tokenized, compiler).map(|items| {
        OvalFile {
            file: source,
            items: items.0,
        }
    })
}
