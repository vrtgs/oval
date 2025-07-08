use crate::compile::tokenizer::TokenKind;
use core::ops::ControlFlow;
use alloc::vec::Vec;
use alloc::vec;
use crate::compile::compiler::Compiler;
use crate::compile::parser::item::Item;
use crate::compile::source_file::SourceFile;
use crate::compile::span::SimpleSpan;
use crate::compile::tokenizer::{TokenStream, TokenTree};
use crate::compile::error::{Error, Result, SyntaxError};

pub mod r#type;
pub mod block;
pub mod item;

#[derive(Debug)]
pub struct OvalFile<'a> {
    file: &'a SourceFile,
    items: Vec<Item>
}

struct Checkpoint<'a> {
    last_end: Option<usize>,
    tokens: &'a [TokenTree]
}

pub(crate) struct Parser<'src, 'tokens, 'compiler> {
    file: &'src SourceFile,
    compiler: &'compiler mut Compiler,
    last_end: Option<usize>,
    tokens: &'tokens [TokenTree]
}

pub(crate) trait ParseAst: Sized + 'static {
    fn parse_inner<'src>(parser: &mut Parser<'src, '_, '_>) -> Result<'src, Self>;
}


pub(crate) trait ListBehaviour {
    type Output<T>;
    type Data;
    const INIT: Self::Data;

    const MUST_EOS: bool;

    fn before_parse(data: &mut Self::Data, parser: &mut Parser) -> ControlFlow<()>;
    fn make_output<T>(data: Self::Data, list: Vec<T>) -> Self::Output<T>;
}

pub(crate) enum AllowTrailing {}

impl ListBehaviour for AllowTrailing {
    type Output<T> = Vec<T>;
    type Data = ();

    const INIT: Self::Data = ();

    const MUST_EOS: bool = false;

    fn before_parse(_: &mut Self::Data, parser: &mut Parser) -> ControlFlow<()> {
        if parser.hit_eos() {
            return ControlFlow::Break(())
        }

        ControlFlow::Continue(())
    }

    fn make_output<T>(_: Self::Data, list: Vec<T>) -> Self::Output<T> {
        list
    }
}


pub(crate) enum DisAllowTrailing {}

impl ListBehaviour for DisAllowTrailing {
    type Output<T> = Vec<T>;
    type Data = ();

    const INIT: Self::Data = ();

    const MUST_EOS: bool = false;

    fn before_parse(_: &mut Self::Data, _: &mut Parser) -> ControlFlow<()> {
        ControlFlow::Continue(())
    }

    fn make_output<T>(_: Self::Data, list: Vec<T>) -> Self::Output<T> {
        list
    }
}



pub(crate) enum TupleOrParens<T> {
    Parens(T),
    Tuple(Vec<T>)
}


pub(crate) enum Tuple {}

impl ListBehaviour for Tuple {
    type Output<T> = TupleOrParens<T>;
    type Data = bool;

    const INIT: Self::Data = false;

    const MUST_EOS: bool = true;

    fn before_parse(trailing_separator: &mut Self::Data, parser: &mut Parser) -> ControlFlow<()> {
        if parser.hit_eos() {
            *trailing_separator = true;
            return ControlFlow::Break(())
        }

        ControlFlow::Continue(())
    }

    fn make_output<T>(trailing_separator: Self::Data, list: Vec<T>) -> Self::Output<T> {
        match trailing_separator {
            true => TupleOrParens::Tuple(list),
            false => match <[T; 1]>::try_from(list) {
                Ok([ty]) =>  TupleOrParens::Parens(ty),
                Err(list) => TupleOrParens::Tuple(list)
            }
        }
    }
}

impl<'src, 'tokens, 'compiler> Parser<'src, 'tokens, 'compiler> {
    pub fn new(compiler: &'compiler mut Compiler, tokens: &'tokens TokenStream<'src>) -> Self {
        Self {
            file: tokens.source,
            compiler,
            last_end: None,
            tokens: &tokens.token_trees,
        }
    }

    pub fn file(&self) -> &'src SourceFile {
        self.file
    }

    pub fn file_span(&self) -> SimpleSpan {
        SimpleSpan::from_range(0..self.file().contents().len())
    }

    pub fn hit_eos(&self) -> bool {
        self.tokens.is_empty()
    }

    pub fn assert_eos(&self) -> Result<'src, ()> {
        match self.peek() {
            Some(tt) => Err(self.syntax_error(SyntaxError::expected_found([None].into_iter(), tt))),
            None => Ok(())
        }
    }

    pub fn checkpoint(&self) -> Checkpoint<'tokens> {
        Checkpoint {
            last_end: self.last_end,
            tokens: self.tokens,
        }
    }

    pub fn restore(&mut self, checkpoint: Checkpoint<'tokens>) {
        self.last_end = checkpoint.last_end;
        self.tokens = checkpoint.tokens
    }

    pub fn peek(&self) -> Option<&'tokens TokenTree> {
        self.tokens.first()
    }

    pub fn eat(&mut self, expected: TokenKind) -> Result<'src, &'tokens TokenTree> {
        let file = self.file;

        self.try_eat(expected).map_err(|found| {
            Error::syntax_error(
                file,
                [SyntaxError::expected_found(
                    [expected].into_iter(),
                    found
                )]
            )
        })
    }

    pub fn maybe_eat(&mut self, expected: TokenKind) -> Option<&'tokens TokenTree> {
        self.try_eat(expected).ok()
    }

    /// # Returns
    /// Ok(last consumed token tree)
    /// Err(peek result)
    pub fn try_eat(&mut self, expected: TokenKind) -> Result<'src, &'tokens TokenTree, Option<&'tokens TokenTree>> {
        self
            .eat_with_inner(|tt, _| (tt.start_token_kind() == expected).then_some(tt))
            .ok_or_else(|| self.peek())
    }

    pub fn eat_with<T>(&mut self, eater: impl FnOnce(&'tokens TokenTree, &mut Self) -> Result<'src, Option<T>>) -> Result<'src, T> {
        let mut error = None;
        self
            .eat_with_inner(|tt, parser| {
                match eater(tt, parser).transpose()? {
                    Ok(x) => Some(x),
                    Err(err) => {
                        error = Some(err);
                        None
                    }
                }
            })
            .ok_or_else(|| error.unwrap_or_else(|| {
                Error::syntax_error(self.file(), [SyntaxError::unexpected_token(self.peek())])
            }))
    }

    fn eat_with_inner<T>(&mut self, eater: impl FnOnce(&'tokens TokenTree, &mut Self) -> Option<T>) -> Option<T> {
        let (head, tail) = self.tokens.split_first()?;
        let ret = eater(head, self)?;
        self.tokens = tail;
        self.last_end = Some(head.span().end());
        Some(ret)
    }

    pub fn next(&mut self) -> Option<&'tokens TokenTree> {
        self.eat_with_inner(|tt, _| Some(tt))
    }


    pub fn parse_spanned<T: ParseAst>(&mut self) -> Result<'src, (T, Option<SimpleSpan>)> {
        let checkpoint = self.checkpoint();
        let start = self.peek().map(|tt| tt.span().start());

        T::parse_inner(self)
            .map(|item| {
                if checkpoint.tokens.len() == self.tokens.len() {
                    return (item, None)
                }

                let end = self.last_end;
                let range = start.and_then(|start| Some(start..end?)).expect({
                    "tokens were consumed; so there should have been a token when peeking, and a last token consumed"
                });

                (item, Some(SimpleSpan::from_range(range)))
            })
            .map_err(|err| {
                self.restore(checkpoint);
                err
            })
    }

    pub fn parse<T: ParseAst>(&mut self) -> Result<'src, T> {
        self.parse_spanned().map(|(x, _)| x)
    }

    fn parse_list_with_inner<T, B: ListBehaviour>(&mut self, separator: TokenKind, mut parse_fn: impl FnMut(&mut Self) -> Result<'src, T>) -> Result<'src, B::Output<T>> {
        if self.hit_eos() {
            return Ok(B::make_output(B::INIT, vec![]))
        }

        let mut trailing_data = B::INIT;
        let mut list = vec![parse_fn(self)?];
        while self.maybe_eat(separator).is_some() {
            if let ControlFlow::Break(()) = B::before_parse(&mut trailing_data, self) {
                break
            }
            let additional = parse_fn(self)?;
            list.push(additional)
        }

        if B::MUST_EOS {
            self.assert_eos()?
        }

        Ok(B::make_output(trailing_data, list))
    }


    pub fn parse_list_with<T, B: ListBehaviour>(&mut self, separator: TokenKind, parse_fn: impl FnMut(&mut Self) -> Result<'src, T>) -> Result<'src, B::Output<T>> {
        let checkpoint = self.checkpoint();
        self.parse_list_with_inner::<T, B>(separator, parse_fn).map_err(|err| {
            self.restore(checkpoint);
            err
        })
    }

    pub fn parse_list<T: ParseAst, B: ListBehaviour>(&mut self, separator: TokenKind) -> Result<'src, B::Output<T>> {
        self.parse_list_with::<T, B>(separator, T::parse_inner)
    }

    pub fn sub_parser(&mut self, tt: &'tokens [TokenTree]) -> Parser<'src, 'tokens, '_> {
        Parser {
            file: self.file,
            compiler: self.compiler,
            last_end: None,
            tokens: tt,
        }
    }

    pub fn syntax_error(&self, err: SyntaxError) -> Error<'src> {
        Error::syntax_error(
            self.file,
            [err]
        )
    }

    pub fn compiler(&mut self) -> &mut Compiler {
        self.compiler
    }
}

pub fn parse<'a>(compiler: &mut Compiler, tokens: TokenStream<'a>) -> Result<'a, OvalFile<'a>> {
    let mut parse = Parser::new(compiler, &tokens);
    let mut items = vec![];
    while !parse.hit_eos() {
        items.push(parse.parse::<Item>()?)
    }

    Ok(OvalFile {
        file: tokens.source,
        items,
    })
}