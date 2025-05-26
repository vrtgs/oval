use std::borrow::Cow;
use std::io;
use std::ops::Range;
use std::path::{Path as FsPath, PathBuf};
use std::sync::LazyLock;
use ariadne::{Label, Report, ReportKind, Source};
use chumsky::error::Rich;
use chumsky::{extra, Parser};
use chumsky::combinator::MapWith;
use chumsky::extra::SimpleState;
use chumsky::input::MapExtra;
use chumsky::prelude::choice;
use chumsky::primitive::just;
use chumsky::span::SimpleSpan;
use crate::parser::interner::{Interner, Symbol};
use crate::parser::tokenizer::{Token, TokenInner};

mod interner;

pub mod tokenizer;

struct TokenTreeParserData<'a> {
    input: &'a str,
    interner: Interner
}

type ParserExtra<'a> = extra::Full<Rich<'a, Token>, SimpleState<TokenTreeParserData<'a>>, ()>;

trait ParseTokenTree<'a>: Sized {
    fn parse() -> impl Parser<'a, &'a [Token], Self, ParserExtra<'a>> + Clone;
}

struct ContextInner {
    input: String,
    interner: Interner
}

pub struct ParserContext(Option<ContextInner>);

impl ParserContext {
    pub fn new() -> Self {
        Self(None)
    }
}

macro_rules! token {
    ($ident: ident) => {const { Token::from_inner(TokenInner::$ident) }};
}

macro_rules! parse_tok {
    ($ident: ident) => {
        const { just(token!($ident)) }
    };
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Ident(Symbol);

impl<'a> ParseTokenTree<'a> for Ident {
    fn parse() -> impl Parser<'a, &'a [Token], Self, ParserExtra<'a>> + Clone {
        parse_tok!(Ident).map_with(|tok, state: &mut MapExtra<_, ParserExtra>| {
            let state = state.state();
            let val = &state.input[tok.span().into_range()];
            Ident(state.interner.interned(val))
        })
    }
}

pub struct Path {
    ident: Ident,
    prefix: Vec<Ident>
}

pub struct ParenType {
    span: SimpleSpan,
    ty: Box<Type>
}

pub struct ArrayType {
    span: SimpleSpan,
    ty: Box<Type>
}

pub struct RefType {
    mutable: bool,
    span: SimpleSpan,
    ty: Box<Type>
}

pub enum Type {
    TypePath(Path),
    Paren(ParenType),
    Array(ArrayType),
    Ref(RefType)
}

pub struct FunctionCall<'a>(Vec<Expr<'a>>);

impl<'a> FunctionCall<'a> {
    pub fn new(func: Expr<'a>, mut args: Vec<Expr<'a>>) -> Self {
        args.push(func);
        Self(args)
    }
    
    pub fn args(&self) -> &[Expr<'a>] {
        let [args @ .., _func] = &*self.0 else { 
            unreachable!()
        };
        
        args
    }
    
    pub fn func(&self) -> &Expr<'a> {
        self.0.last().unwrap()
    }
}

pub enum Expr<'a> {
    Str(Cow<'a, str>),
    Char(char),
    Body(Body<'a>),
    Ident(Ident),
    
    
    Add(Box<(Expr<'a>, Expr<'a>)>),
    Sub(Box<(Expr<'a>, Expr<'a>)>),
    Mul(Box<(Expr<'a>, Expr<'a>)>),
    Div(Box<(Expr<'a>, Expr<'a>)>),
    Mod(Box<(Expr<'a>, Expr<'a>)>),
    EMod(Box<(Expr<'a>, Expr<'a>)>),
    EDiv(Box<(Expr<'a>, Expr<'a>)>),
    
    // Unary
    Deref(Box<Expr<'a>>),
    Neg(Box<Expr<'a>>),

    FunctionCall(FunctionCall<'a>),
}


fn parse_quoted<'a>(token: TokenInner) -> impl Parser<'a, &'a [Token], Cow<'a, str>, ParserExtra<'a>> + Clone {
    just(Token::from_inner(token)).validate(|tok, state: &mut MapExtra<_, ParserExtra>, emitter| {
        let full_literal = &state.state().input[tok.span().into_range()];

        let mut last_block_start = 0_usize;
        let mut str = full_literal.chars();
        let mut owned = String::new();

        while let Some(char) = str.next() {
            if char == '\\' {
                let escape_start = full_literal.len() - str.as_str().len() - 1;
                
                let mut insert_to_text = |ch: char| {
                    let str: &str = &full_literal[last_block_start..escape_start];
                    owned.reserve(str.len() + ch.len_utf8());
                    owned.push_str(str);
                    owned.push(ch);
                };
                
                match str.next() {
                    Some('n') => insert_to_text('\n'),
                    Some('r') => insert_to_text('\r'),
                    Some('t') => insert_to_text('\r'),
                    Some('0') => insert_to_text('\0'),
                    Some('u') => todo!(),
                    Some('\'') => insert_to_text('\''),
                    Some('"') => insert_to_text('"'),
                    Some(unexpected) => {
                        emitter.emit(Rich::custom(
                            SimpleSpan {
                                start: escape_start,
                                end: escape_start + unexpected.len_utf8(),
                                context: (),
                            },
                            format_args!("invalid escape sequence {unexpected}")
                        ));
                        
                        return Cow::Borrowed(full_literal)
                    },
                    None => unreachable!("unescaped strings aren't allowed by the tokenizer")
                }

                last_block_start = full_literal.len() - str.as_str().len();
            }
        }

        match last_block_start { 
            0 => {
                debug_assert!(owned.is_empty());
                Cow::Borrowed(full_literal)
            }
            _ => {
                debug_assert!(!owned.is_empty());
                owned.push_str(&full_literal[last_block_start..]);
                Cow::Owned(owned)
            }
        }
    })
}

fn parse_str_lit<'a>() -> impl Parser<'a, &'a [Token], Cow<'a, str>, ParserExtra<'a>> + Clone {
    parse_quoted(TokenInner::StringLiteral)
}

fn parse_char_lit<'a>() -> impl Parser<'a, &'a [Token], char, ParserExtra<'a>> + Clone {
    parse_quoted(TokenInner::CharLiteral).validate(|f, extra, emit| {
        let mut chars = f.chars();
        match chars.next() { 
            None => {
                emit.emit(Rich::custom(
                    extra.span(),
                    "empty char literals are not allowed"
                ));
                
                '\0'
            },
            Some(chr) => match chars.next() {
                None => chr,
                Some(_) => {
                    emit.emit(Rich::custom(
                        extra.span(),
                        "too many character (unicode-code scalar value) in character literal"
                    ));
                    chr
                }
            }
        }
    })
}

impl<'a> ParseTokenTree<'a> for Expr<'a> {
    fn parse() -> impl Parser<'a, &'a [Token], Self, ParserExtra<'a>> + Clone {
        use chumsky::pratt::*;
        use chumsky::recursive::recursive;
        use chumsky::IterParser;

        macro_rules! inverted_assoc {
            ($expr:expr) => {const { u16::MAX - $expr }};
        }
        
        macro_rules! op {
            ($ident: ident) => {
                const { just(token!($ident)) }
            };
        }

        recursive(|expr| {
            let choices = choice((
                parse_str_lit().map(Expr::Str),
                parse_char_lit().map(Expr::Char),
                Ident::parse().map(Expr::Ident),
                expr.clone().delimited_by(parse_tok!(RParen), parse_tok!(LParen)),
                expr.clone().then({
                    expr
                        .clone()
                        .separated_by(parse_tok!(Comma))
                        .allow_trailing()
                        .collect::<Vec<_>>()
                        .delimited_by(parse_tok!(RParen), parse_tok!(LParen))
                }).map(|(func, args)| {
                    Expr::FunctionCall(FunctionCall::new(func, args))
                }),
                expr
                    .separated_by(parse_tok!(SemiColon).repeated())
                    .allow_leading()
                    .collect::<Vec<_>>()
                    .then(parse_tok!(SemiColon).repeated().or_not())
                    .map(|(expressions, leading)| {
                    })
            ));

            const UNARY: u16 = inverted_assoc!(0);


            choices.pratt((
                prefix(UNARY, op!(Deref), |_, expr, _| Expr::Deref(Box::new(expr))),
                
            ))
        })
    }
}

pub struct Body<'a> {
    is_terminated: bool,
    expr: Box<[Expr<'a>]>
}

impl<'a> Body<'a> {

}

pub struct OvalFunction<'a> {
    name: Ident,
    args: Vec<(Ident, Type)>,
    ret: Type,
    body: Body<'a>
}

pub enum OvalItem<'a> {
    Function(OvalFunction<'a>),

}

pub struct OvalFile<'a> {
    items: Vec<OvalItem<'a>>
}

pub enum ErrorKind<'a> {
    Io(io::Error),
    Syntax {
        source: Source<&'a str>,
        errors: Vec<Rich<'a, char>>
    }
}

struct ParseErrorInner<'a> {
    file: Option<PathBuf>,
    error: ErrorKind<'a>
}

pub struct ParseError<'a>(Box<ParseErrorInner<'a>>);

impl<'a> From<ParseErrorInner<'a>> for ParseError<'a> {
    fn from(value: ParseErrorInner<'a>) -> Self {
        Self(Box::new(value))
    }
}

impl<'a> ParseError<'a> {
    pub fn file_name(&self) -> &str {
        self.0.file.as_ref()
            .and_then(|path| path.file_name())
            .and_then(|os_str| os_str.to_str())
            .unwrap_or("<unknown>")
    }



    pub fn source(&self) -> &Source<&str> {
        match self.0.error {
            ErrorKind::Io(_) => {
                static EMPTY_SOURCE: LazyLock<Source<&str>> = LazyLock::new(|| {
                    Source::from("")
                });

                &EMPTY_SOURCE
            },
            ErrorKind::Syntax { ref source, .. } => source,
        }
    }

    pub fn error_reports(&self) -> impl Iterator<Item=Report<'_, (&'_ str, Range<usize>)>> {
        let file_name = self.file_name();

        let errors = match &self.0.error {
            ErrorKind::Io(io_err) => {
                let err = Report::build(ReportKind::Error, (file_name, 0..0))
                    .with_code(0)
                    .with_label(Label::new((file_name, 0..0)).with_message(io_err))
                    .finish();

                vec![err]
            }
            ErrorKind::Syntax { errors, .. } => {
                let errors_iter = errors.iter().map(|error| {
                    let span = error.span();
                    Report::build(ReportKind::Error, (file_name, span.into_range()))
                        .with_code(1)
                        .with_message("tokenization failure")
                        .with_label({
                            Label::new((file_name, span.into_range()))
                                .with_message(error.reason())
                        })
                        .finish()
                });
                errors_iter.collect()
            }
        };

        errors.into_iter()
    }
}

pub type Result<'a, T> = std::result::Result<T, ParseError<'a>>;


fn parse_file_inner<'ctx>(path: &FsPath, context: &'ctx mut ParserContext) -> Result<'ctx, OvalFile<'ctx>> {
    let make_error = move |error_kind| ParseError::from(ParseErrorInner {
        file: Some(path.to_path_buf()),
        error: error_kind
    });

    let file = std::fs::read_to_string(path).map_err(ErrorKind::Io).map_err(make_error)?;
    let ctx = context.0.insert(ContextInner {
        input: file,
        interner: Interner::new(),
    });

    let input = &*ctx.input;
    let tokens = match tokenizer::tokenize(input).into_result() {
        Ok(tokens) => tokens,
        Err(errors) => return Err(make_error(ErrorKind::Syntax {
            source: Source::from(input),
            errors
        }))
    };

    todo!()
}

pub fn parse_file<P: AsRef<FsPath>>(path: P, context: &mut ParserContext) -> Result<OvalFile> {
    parse_file_inner(path.as_ref(), context)
}