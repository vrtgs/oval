use alloc::vec;
use alloc::vec::Vec;
use alloc::format;
use core::fmt::{Debug, Formatter};
use core::str::Chars;
use crate::compile;
use crate::compile::error::{Result, SyntaxError};
use crate::compile::source_file::SourceFile;
use crate::compile::span::{FullSpan, SimpleSpan};


#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum LiteralKind {
    String { terminated: bool },
    Char { terminated: bool },
    Float,
    Int
}

macro_rules! make_token {
    (enum $enum:ident, $enum2:ident {
        $({$($tt:tt)*})*
    }) => {
        make_token! {
            $enum,
            $enum2,
            acc: { $({$($tt)*})* }
            keywords: {}
            parens: {}
            string_based: {}
        }
    };

    (
        $enum:ident,
        $enum2:ident,
        acc: { { KW: $new_kw_name:ident = $new_kw:literal } $($rest:tt)* }
        keywords: { $($kw_name:ident = $kw:literal),* }
        parens: { $($paren_name:ident = [$r_paren:literal, $l_paren: literal]),* }
        string_based: { $($str_name:ident = [$($str:literal),+]),* }
    ) => {
        make_token! {
            $enum,
            $enum2,
            acc: { $($rest)* }
            keywords: { $($kw_name = $kw,)* $new_kw_name = $new_kw }
            parens: { $($paren_name = [$r_paren, $l_paren]),* }
            string_based: { $($str_name = [$($str),+]),* }
        }
    };

    (
        $enum:ident,
        $enum2:ident,
        acc: { { paren: $new_paren_name:ident, $new_paren_str_name: literal = [$new_r_paren:literal, $new_l_parent:literal] } $($rest:tt)* }
        keywords: { $($kw_name:ident = $kw:literal),* }
        parens: { $($paren_name:ident, $paren_str_name:literal = [$r_paren:literal, $l_paren: literal]),* }
        string_based: { $($str_name:ident = [$($str:literal),+]),* }
    ) => {
        make_token! {
            $enum,
            $enum2,
            acc: { $($rest)* }
            keywords: { $($kw_name = $kw),* }
            parens: { $($paren_name, $paren_str_name = [$r_paren, $l_paren],)*  $new_paren_name, $new_paren_str_name = [$new_r_paren, $new_l_parent] }
            string_based: { $($str_name = [$($str),+]),* }
        }
    };

    (
        $enum:ident,
        $enum2:ident,
        acc: { { $new_str_name:ident = [$($new_str:literal),+] } $($rest:tt)* }
        keywords: { $($kw_name:ident = $kw:literal),* }
        parens: { $($paren_name:ident, $paren_str_name:literal = [$r_paren:literal, $l_paren: literal]),* }
        string_based: { $($str_name:ident = [$($str:literal),+]),* }
    ) => {
        make_token! {
            $enum,
            $enum2,
            acc: { $($rest)* }
            keywords: { $($kw_name = $kw),* }
            parens: { $($paren_name, $paren_str_name = [$r_paren, $l_paren]),* }
            string_based: { $($str_name = [$($str),+],)* $new_str_name = [$($new_str),+] }
        }
    };
    
    (
        $token_kind:ident,
        $token_tree_kind:ident,
        acc: {}
        keywords: { $($kw_name:ident = $kw:literal),* }
        parens: { $($paren_name:ident, $paren_str_name:literal = [$r_paren:literal, $l_paren: literal]),* }
        string_based: { $($str_name:ident = [$first_char: literal $(, $suffix_str:literal)?]),* }
    ) => {
        paste::paste! {
            #[derive(Copy, Clone, Debug, PartialEq)]
            pub enum $token_kind {
                Ident,
                Literal(LiteralKind),
                LineComment,
                BlockComment {
                    terminated: bool
                },
                $([<R $paren_name>], [<L $paren_name>],)*
                $($kw_name,)*
                $($str_name,)*
                Unknown(char)
            }
        }

        #[derive(Clone, Debug)]
        pub enum $token_tree_kind {
            Ident,
            Literal(LiteralKind),
            $($paren_name(Vec<TokenTree>),)*
            $($kw_name,)*
            $($str_name,)*
        }


        struct Tokens<'a> {
            file: &'a str,
            chars: Chars<'a>
        }

        impl<'a> Iterator for Tokens<'a> {
            type Item = Token;

            fn next(&mut self) -> Option<Self::Item> {
                let file_chars = &mut self.chars;
                
                let offset = self.file.len();
                let chars_to_offset = |chars: &Chars| offset - chars.as_str().len();

                'tokenizing:
                while let Some(ch) = file_chars.next() {
                    // filter whitespace
                    if ch.is_whitespace() {
                        continue 'tokenizing
                    }

                    // subtract the char just consumed
                    let start = chars_to_offset(&file_chars) - ch.len_utf8();

                    let token_span = |chars_now| start..chars_to_offset(chars_now);
                    
                    let make_token = |token_type, chars_now| {
                        Token {
                            span: SimpleSpan::from_range(token_span(chars_now)),
                            kind:token_type,
                        }
                    };

                    // filter comments
                    if ch == '/' {
                        let prev = file_chars.clone();
                        match file_chars.next() {
                            Some('/') => {
                                let str = file_chars.as_str();
                                match str.find('\n') {
                                    Some(i) => *file_chars = str[i+1..].chars(),
                                    None => *file_chars = "".chars()
                                }

                                return Some(make_token(TokenKind::LineComment, &file_chars));
                            },
                            Some('*') => {
                                let str = file_chars.as_str();
                                let terminated = match str.find("*/") {
                                    Some(i) => {
                                        *file_chars = str[i+2..].chars();
                                        true
                                    },
                                    None => {
                                        *file_chars = "".chars();
                                        false
                                    }
                                };

                                return Some(make_token(TokenKind::BlockComment { terminated }, &file_chars));
                            }
                            _ => *file_chars = prev
                        }
                    }

                    let token = match ch {
                        'a'..='z' | 'A'..='Z' | '_' => {
                            while let Some('a'..='z' | 'A'..='Z' | '0'..='9' | '_') = file_chars.clone().next() {
                                file_chars.next();
                            }

                            let range = token_span(&file_chars);
                            let token_ty = match &self.file[range] {
                                $($kw => TokenKind::$kw_name,)*
                                _ => TokenKind::Ident
                            };
                            
                            make_token(token_ty, &file_chars)
                        }
                        '0'..='9' => {
                            let mut radix = 10;

                            if ch == '0' {
                                let prev = file_chars.clone();
                                match file_chars.next() {
                                    Some('b') => radix = 2,
                                    Some('o') => radix = 8,
                                    Some('x') => radix = 16,
                                    _ => *file_chars = prev
                                }
                            }

                            let next_digit = |chars: &mut Chars| {
                                chars.next().is_some_and(|ch| ch.is_digit(radix))
                            };

                            while next_digit(&mut file_chars.clone()) {
                                file_chars.next();
                            }

                            let mut lit_kind = LiteralKind::Int;
                            let mut float_check = file_chars.clone();
                            // TODO: scientific notation
                            if radix == 10 && float_check.next() == Some('.') {
                                if next_digit(&mut float_check) {
                                    lit_kind = LiteralKind::Float;
                                    *file_chars = float_check;

                                    while next_digit(&mut file_chars.clone()) {
                                        file_chars.next();
                                    }
                                }
                            }

                            make_token(TokenKind::Literal(lit_kind), &file_chars)
                        }
                        '"' | '\'' => {
                            let mut terminated = false;
                            while let Some(str_ch) = file_chars.next() {
                                if str_ch == ch {
                                    terminated = true;
                                    break
                                }

                                if str_ch == '\\' {
                                    // just skip the next char without checking for quotes
                                    file_chars.next();
                                }
                            }

                            let lit_kind = match ch {
                                '"' => LiteralKind::String { terminated },
                                '\'' => LiteralKind::Char { terminated },
                                _ => unreachable!()
                            };

                            make_token(TokenKind::Literal(lit_kind), &file_chars)
                        }
                        $(
                        $r_paren => make_token(paste::paste! { TokenKind::[<R $paren_name>] }, &file_chars),
                        $l_paren => make_token(paste::paste! { TokenKind::[<L $paren_name>] }, &file_chars),
                        )*
                        #[allow(unused_labels)]
                        unknown => 'ret_unknown: {
                            $(
                                'check_token: {
                                    if unknown == $first_char {
                                        $(
                                        let Some(suffix) = file_chars.as_str().strip_prefix($suffix_str) else {
                                            break 'check_token
                                        };
                                        *file_chars = suffix.chars();
                                        )?
                                        
                                        break 'ret_unknown make_token(TokenKind::$str_name, &file_chars);
                                    }
                                }
                            )*

                            make_token(TokenKind::Unknown(unknown), &file_chars)
                        }
                    };
                    
                    return Some(token);
                }
                
                None
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                let str = self.chars.as_str();
                (
                    (!str.is_empty()) as usize,
                    Some(str.len())
                )
            }
        }

        pub(crate) fn tokenize(file: &str) -> impl Iterator<Item=Token> {
            Tokens {
                file,
                chars: file.chars()
            }
        }
        
        
        pub(crate) fn normalize_tokens(tokenized: TokenizedSource) -> Result<TokenStream> {
            enum ParenKind { 
                $($paren_name),*
            }
            
            impl ParenKind {
                fn name(self) -> &'static str {
                    match self {
                        $(Self::$paren_name => $paren_str_name),*
                    }
                }
            }

            struct ParenStackEntry {
                span_start: SimpleSpan,
                paren_kind: ParenKind,
                tokens: Vec<TokenTree>
            }

            let mut errors = vec![];
            let mut paren_stack: Vec<ParenStackEntry> = vec![];
            let mut tokens = vec![];
            
            fn active_stack<'a>(tokens: &'a mut Vec<TokenTree>, paren_stack: &'a mut Vec<ParenStackEntry>) -> &'a mut Vec<TokenTree> { 
                paren_stack
                    .last_mut()
                    .map(|entry| &mut entry.tokens)
                    .unwrap_or(tokens)
            }

            let source = tokenized.source;

            'parsing:
            for token in tokenized.tokens {
                let span = token.span;

                let merge_span_back = |span2: SimpleSpan| {
                    SimpleSpan::from_range(span2.start()..span.end())
                };
                
                let kind = paste::paste! {
                    match token.kind {
                        TokenKind::Ident => TokenTreeKind::Ident,
                        TokenKind::Literal(lit_kind) => TokenTreeKind::Literal(lit_kind),
                        $(TokenKind::$kw_name => TokenTreeKind::$kw_name,)*
                        $(TokenKind::$str_name => TokenTreeKind::$str_name,)*
                        
                        TokenKind::BlockComment { terminated } => {
                            if !terminated {
                                errors.push(SyntaxError {
                                    span,
                                    message: "unterminated block comment".into(),
                                })
                            }
                            continue 'parsing
                        }
                        TokenKind::LineComment => continue 'parsing,
                        TokenKind::Unknown(ch) => {
                            errors.push(SyntaxError {
                                span,
                                message: format!("unexpected {ch}").into()
                            });
                            continue 'parsing
                        }
                        
                        $(
                        TokenKind::[<R $paren_name>] => {
                            paren_stack.push(ParenStackEntry {
                                span_start: span,
                                paren_kind: ParenKind::$paren_name,
                                tokens: vec![],
                            });
                            continue 'parsing
                        }
                        TokenKind::[<L $paren_name>] => {
                            #[allow(unreachable_patterns)]
                            let (span_start, message) = match paren_stack.pop() {
                                Some(ParenStackEntry { span_start, paren_kind: ParenKind::$paren_name, tokens: paren_tokens }) => {
                                    active_stack(&mut tokens, &mut paren_stack).push(TokenTree {
                                        span: merge_span_back(span_start),
                                        kind: TokenTreeKind::Paren(paren_tokens)
                                    });
                                    continue 'parsing
                                }
                                
                                Some(ParenStackEntry { span_start, paren_kind, .. }) => {
                                    (span_start, format!(concat!("mismatched closing delimiter; expected ", "paren", " {}"), paren_kind.name()))
                                }
                                
                                None => {
                                    errors.push(SyntaxError {
                                        span,
                                        message: "unbalanced paren".into()
                                    });
                                    continue 'parsing
                                }
                            };

                            errors.push(SyntaxError {
                                span: merge_span_back(span_start),
                                message: message.into()
                            });
                            continue 'parsing
                        },)*
                    }
                };

                active_stack(&mut tokens, &mut paren_stack).push(TokenTree {
                    span,
                    kind,
                })
            }

            if !errors.is_empty() {
                return Err(compile::error::Error::from(compile::error::ErrorKind::Syntax {
                    source,
                    errors,
                }))
            }

            Ok(TokenStream {
                source,
                tokens,
            })
        }
    };
}

make_token! {
    enum TokenKind, TokenTreeKind {
        { KW: Let   = "let"  }
        { KW: Ref   = "ref"  }
        { KW: Mut   = "mut"  }
        { KW: Fun   = "fun"  }
        { KW: If    = "if"   }
        { KW: Else  = "else" }
        { KW: Loop  = "loop" }
        { KW: Where = "where" }

        { paren: Paren, "paren"     = ['(', ')'] }
        { paren: Bracket, "bracket" = ['{', '}'] }
        { paren: Brace, "brace"     = ['[', ']'] }

        // Control
        { Arrow = ['-', ">"] }
        { Comma = [','] }
        { DoubleColon = [':', ":"] }
        { Colon = [':'] }
        { SemiColon = [';'] }

        // Operators:

        // Cmp
        { Equality = ['=', "="] }
        { Assign   = ['='] }

        { Le = ['<', "="] }
        { Lt = ['<']  }
        { Ge = ['>', "="] }
        { Gt = ['>']  }

        // Arithmetic
        { EMod = ['%', "%"] }
        { EDiv = ['/', "%"] }

        { Plus = ['+'] }
        { Minus = ['-'] }
        { Star = ['*'] }
        { Div = ['/'] }
        { Mod = ['%'] }
    }
}


#[derive(Debug, Copy, Clone)]
pub struct Token {
    span: SimpleSpan,
    kind: TokenKind,
}

#[derive(Debug, Clone)]
pub struct TokenTree {
    span: SimpleSpan,
    kind: TokenTreeKind,
}

impl Token {
    pub fn span(&self) -> SimpleSpan {
        self.span
    }

    pub fn kind(&self) -> TokenKind {
        self.kind
    }
}

impl TokenTree {
    pub fn span(&self) -> SimpleSpan {
        self.span
    }

    pub fn kind(&self) -> &TokenTreeKind {
        &self.kind
    }
}

macro_rules! make_view {
    (
        $($(#[$($meta:tt)*])*
        pub struct $view_name:ident $(<$($other_life: lifetime)*>)? ($field_name: ident : ($ty:ty, $kind_ty:ty));)+
    ) => {$(
        #[derive(Copy, Clone)]
        $(#[$($meta)*])*
        pub struct $view_name<$($($other_life,)*)? 'src> {
            source: &'src SourceFile,
            $field_name: $ty
        }
        
        impl<$($($other_life,)*)? 'src> $view_name<$($($other_life,)*)? 'src> {
            paste::paste! {
                pub fn [<as_ $field_name>](&self) -> $ty {
                    self.$field_name
                }
            }
            
            pub fn kind(&self) -> &$kind_ty {
                &self.$field_name.kind
            }

            pub fn span(&self) -> FullSpan<'src> {
                self.simple_span().into_full(self.source)
            }

            pub fn simple_span(&self) -> SimpleSpan {
                self.$field_name.span
            }

            pub fn view(&self) -> &'src str {
                self.span().slice()
            }
        }
        
        impl<$($($other_life,)*)? 'src> Debug for $view_name<$($($other_life,)*)? 'src> {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                f
                    .debug_struct(stringify!($view_name))
                    .field("span", &self.simple_span())
                    .field("kind", self.kind())
                    .field("view", &self.view())
                    .finish()
            }
        }
    )+};
}

make_view!{
    pub struct TokenView(token: (Token, TokenKind));
    pub struct TokenTreeView<'stream>(token_tree: (&'stream TokenTree, TokenTreeKind));
}

pub struct TokenizedSource<'a> {
    source: &'a SourceFile,
    tokens: Vec<Token>,
}

pub struct TokenStream<'a> {
    source: &'a SourceFile,
    tokens: Vec<TokenTree>,
}

impl<'a> TokenizedSource<'a> {
    pub(crate) fn new(source: &'a SourceFile) -> Self {
        Self {
            source,
            tokens: tokenize(source.contents()).collect()
        }
    }
    
    pub fn tokens(&self) -> impl Iterator<Item=TokenView<'a>> + DoubleEndedIterator + ExactSizeIterator {
        let source = self.source;
        self.tokens.iter().map(move |&token| TokenView {
            source,
            token,
        })
    }
    
    pub fn into_stream(self) -> Result<'a, TokenStream<'a>> {
        normalize_tokens(self)
    }
}

impl<'src> TokenStream<'src> {
    pub fn stream<'stream>(&'stream self) -> impl Iterator<Item=TokenTreeView<'stream, 'src>> + DoubleEndedIterator + ExactSizeIterator {
        let source = self.source;
        self.tokens.iter().map(move |token_tree| TokenTreeView {
            source,
            token_tree,
        })
    }
}
