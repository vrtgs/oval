use alloc::vec::Vec;
use chumsky::error::Rich;
use chumsky::extra::SimpleState;
use chumsky::input::{MapExtra, ValueInput};
use chumsky::{IterParser, Parser};
use chumsky::combinator::{DelimitedBy, MapWith};
use chumsky::prelude::{choice, just};
use chumsky::primitive::Just;
use chumsky::recursive::Recursive;
use chumsky::span::SimpleSpan;
use crate::compile::compiler::Compiler;
use crate::compile::error::Error;
use crate::compile::parser::block::Block;
use crate::compile::parser::block::expr::Expr;
use crate::compile::parser::item::{ConstItem, FunctionItem, Item};
use crate::compile::parser::sealed::SealedParseAst;
use crate::compile::source_file::SourceFile;
use crate::compile::Spanned;
use crate::compile::tokenizer::{Token, TokenizedSource};

pub mod block;
pub mod r#type;
pub mod item;

pub(crate) type ParserExtra<'a> = chumsky::extra::Full<Rich<'a, Token, SimpleSpan>, SimpleState<(&'a SourceFile<'a>, &'a mut Compiler)>, ()>;

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

    fn spanned(self) -> MapWith<Self, O, impl Fn(O, &mut MapExtra<'a, '_, I, ParserExtra<'a>>) -> Spanned<O> + Copy + Send + Sync> {
        self.map_with(|value, extra| Spanned {
            span: extra.span(),
            value,
        })
    }
}

impl<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>, O, P: Parser<'a, I, O, ParserExtra<'a>> + Sized> OvalParserExt <'a, I, O> for P {}

pub(crate) mod sealed {
    use chumsky::input::ValueInput;
    use chumsky::Parser;
    use chumsky::prelude::SimpleSpan;
    use crate::compile::parser::{OvalParserExt, ParserExtra};
    use crate::compile::Spanned;
    use crate::compile::tokenizer::Token;

    pub trait SealedParseAst: Sized + 'static {
        fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone;
    }

    impl<T: SealedParseAst> SealedParseAst for Spanned<T> {
        fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
            T::parser().spanned()
        }
    }
}

pub trait ParseAst: SealedParseAst {}

impl<S: SealedParseAst> ParseAst for S {}

fn make_recursive_parsers<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> (
    impl Parser<'a, I, Expr, ParserExtra<'a>> + Clone,
    impl Parser<'a, I, Block, ParserExtra<'a>> + Clone,
    impl Parser<'a, I, FunctionItem, ParserExtra<'a>> + Clone,
    impl Parser<'a, I, ConstItem, ParserExtra<'a>> + Clone,
    impl Parser<'a, I, Item, ParserExtra<'a>> + Clone,
) {
    let mut block = Recursive::declare();
    let expr = Expr::make_parser(block.clone());
    let func_item = FunctionItem::make_parser(block.clone());
    let const_item = ConstItem::make_parser(expr.clone());
    let item = choice((
        func_item.clone().map(Item::Function),
        const_item.clone().map(Item::Const)
    ));

    block.define(Block::make_parser(expr.clone(), item.clone()));

    (
        expr,
        block,
        func_item,
        const_item,
        item
    )
}

pub fn parse<'a, O: ParseAst>(tokenized: TokenizedSource<'a>, compiler: &mut Compiler) -> Result<O, Error<'a>> {
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
    pub source: &'a SourceFile<'a>,
    pub items: Vec<Item>
}

pub fn parse_file<'a>(tokenized: TokenizedSource<'a>, compiler: &mut Compiler) -> Result<OvalFile<'a>, Error<'a>> {
    struct Items(Vec<Item>);

    impl SealedParseAst for Items {
        fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
            Item::parser().repeated().collect().map(Items)
        }
    }

    let source = tokenized.source();
    parse::<Items>(tokenized, compiler).map(|items| {
        OvalFile {
            source,
            items: items.0,
        }
    })
}
