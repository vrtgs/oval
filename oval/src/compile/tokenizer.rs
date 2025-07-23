use crate::compile::Spanned;
use crate::compile::source::Source;
use alloc::vec;
use alloc::vec::Vec;
use chumsky::error::Rich;
use chumsky::span::SimpleSpan;
use core::fmt::{Debug, Formatter};
use core::str::Chars;

macro_rules! make_token {
    (enum $enum:ident {
        $({$($tt:tt)*})*
    }) => {
        make_token! {
            $enum,
            acc: { $({$($tt)*})* }
            keywords: {}
            parens: {}
            string_based: {}
        }
    };

    (
        $enum:ident,
        acc: { { KW: $new_kw_name:ident = $new_kw:literal } $($rest:tt)* }
        keywords: { $($kw_name:ident = $kw:literal),* }
        parens: { $($paren_name:ident = [$r_paren:literal, $l_paren: literal]),* }
        string_based: { $($str_name:ident = [$($str:literal),+]),* }
    ) => {
        make_token! {
            $enum,
            acc: { $($rest)* }
            keywords: { $($kw_name = $kw,)* $new_kw_name = $new_kw }
            parens: { $($paren_name = [$r_paren, $l_paren]),* }
            string_based: { $($str_name = [$($str),+]),* }
        }
    };

    (
        $enum:ident,
        acc: { { paren: $new_paren_name:ident, $new_paren_str_name: literal = [$new_r_paren:literal, $new_l_parent:literal] } $($rest:tt)* }
        keywords: { $($kw_name:ident = $kw:literal),* }
        parens: { $($paren_name:ident, $paren_str_name:literal = [$r_paren:literal, $l_paren: literal]),* }
        string_based: { $($str_name:ident = [$($str:literal),+]),* }
    ) => {
        make_token! {
            $enum,
            acc: { $($rest)* }
            keywords: { $($kw_name = $kw),* }
            parens: { $($paren_name, $paren_str_name = [$r_paren, $l_paren],)*  $new_paren_name, $new_paren_str_name = [$new_r_paren, $new_l_parent] }
            string_based: { $($str_name = [$($str),+]),* }
        }
    };

    (
        $enum:ident,
        acc: { { $new_str_name:ident = [$($new_str:literal),+] } $($rest:tt)* }
        keywords: { $($kw_name:ident = $kw:literal),* }
        parens: { $($paren_name:ident, $paren_str_name:literal = [$r_paren:literal, $l_paren: literal]),* }
        string_based: { $($str_name:ident = [$($str:literal),+]),* }
    ) => {
        make_token! {
            $enum,
            acc: { $($rest)* }
            keywords: { $($kw_name = $kw),* }
            parens: { $($paren_name, $paren_str_name = [$r_paren, $l_paren]),* }
            string_based: { $($str_name = [$($str),+],)* $new_str_name = [$($new_str),+] }
        }
    };

    (
        $token:ident,
        acc: {}
        keywords: { $($kw_name:ident = $kw:literal),* }
        parens: { $($paren_name:ident, $paren_str_name:literal = [$l_paren:literal, $r_paren: literal]),* }
        string_based: { $($str_name:ident = [$first_char: literal $(, $suffix_str:literal)?]),* }
    ) => {
        paste::paste! {
            #[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
            pub enum $token {
                Ident,
                String,
                Char,
                Number,
                $([<L $paren_name>], [<R $paren_name>],)*
                $($kw_name,)*
                $($str_name,)*
            }

            impl $token {
                pub fn repr(self) -> &'static str {
                    match self {
                        Self::Ident => "identifier",
                        Self::String => "string literal",
                        Self::Char => "character literal",
                        Self::Number => "number literal",
                        $(
                        Self::[<L $paren_name>] => concat!($l_paren, ""),
                        Self::[<R $paren_name>] => concat!($r_paren, ""),
                        )*
                        $(Self::$kw_name => $kw,)*
                        $(Self::$str_name => concat!(stringify!($first_char) $(, $suffix_str)? ),)*
                    }
                }
            }
        }

        impl core::fmt::Display for $token {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                f.write_str(self.repr())
            }
        }

        #[derive(Clone)]
        struct Tokens<'a> {
            file: &'a str,
            chars: Chars<'a>
        }

        pub(crate) enum TokenizerError {
            Unknown(char),
            Unterminated { name: &'static str }
        }

        impl<'a> Iterator for Tokens<'a> {
            type Item = Spanned<Result<$token, TokenizerError>>;

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

                    let make_maybe_token = |value, chars_now| {
                        Spanned {
                            span: SimpleSpan::from(token_span(chars_now)),
                            value,
                        }
                    };

                    let make_token = |token, chars_now| {
                        make_maybe_token(Ok(token), chars_now)
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

                                continue 'tokenizing
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

                                if !terminated {
                                    return Some(make_maybe_token(Err(TokenizerError::Unterminated { name: "block comment" }), &file_chars));
                                }

                                continue 'tokenizing
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
                                $($kw => $token::$kw_name,)*
                                _ => $token::Ident
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


                            let next_digit_with_radix = |chars: &mut Chars, with_radix: u32| {
                                chars.next().is_some_and(|ch| ch.is_digit(with_radix))
                            };

                            let next_digit = |chars: &mut Chars| next_digit_with_radix(chars, radix);

                            while next_digit(&mut file_chars.clone()) {
                                file_chars.next();
                            }

                            let mut float_check = file_chars.clone();
                            if float_check.next() == Some('.') {
                                if next_digit_with_radix(&mut float_check, 10) {
                                    *file_chars = float_check;

                                    while next_digit_with_radix(&mut file_chars.clone(), 10) {
                                        file_chars.next();
                                    }
                                }
                            }

                            // parse exponent
                            if let Some('e' | 'E') =  file_chars.clone().next() {
                                file_chars.next();
                                while let Some('0'..='9') = file_chars.clone().next() {
                                    file_chars.next();
                                }
                            }

                            // parse suffix
                            if let Some('a'..='z' | 'A'..='Z' | '_') = file_chars.clone().next() {
                                file_chars.next();
                                while let Some('a'..='z' | 'A'..='Z' | '0'..='9' | '_') = file_chars.clone().next() {
                                    file_chars.next();
                                }
                            }

                            make_token(Token::Number, &file_chars)
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
                                '"' => Token::String,
                                '\'' => Token::Char,
                                _ => unreachable!()
                            };

                            let maybe_token = match terminated {
                                true => Ok(lit_kind),
                                false => Err(TokenizerError::Unterminated { name: lit_kind.repr() })
                            };

                            make_maybe_token(maybe_token, &file_chars)
                        }
                        $(
                        $l_paren => make_token(paste::paste! { $token::[<L $paren_name>] }, &file_chars),
                        $r_paren => make_token(paste::paste! { $token::[<R $paren_name>] }, &file_chars),
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

                                        break 'ret_unknown make_token($token::$str_name, &file_chars);
                                    }
                                }
                            )*

                            make_maybe_token(Err(TokenizerError::Unknown(unknown)), &file_chars)
                        }
                    };

                    return Some(token);
                }

                None
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (0, Some(self.chars.as_str().len()))
            }
        }

        pub(crate) fn tokenize(file: &str) -> impl Iterator<Item=Spanned<Result<$token, TokenizerError>>> + Clone {
            Tokens {
                file,
                chars: file.chars()
            }
        }

        fn normalize_tokens<'a>(source: Source<'a>, tokens_iter: impl Iterator<Item=Spanned<Result<$token, TokenizerError>>>) -> $crate::compile::error::Result<'a, Vec<Spanned<Token>>> {
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
            }

            let mut paren_stack: Vec<ParenStackEntry> = vec![];
            let mut errors = vec![];
            let mut tokens = vec![];

            'parsing:
            for token in tokens_iter {
                let span = token.span;

                let merge_span_back = |span2: SimpleSpan| {
                    SimpleSpan::from(span2.start..span.end)
                };

                let token = match token.value {
                    Ok(x) => x,
                    Err(TokenizerError::Unknown(ch)) => {
                        errors.push(Rich::custom(
                            span,
                            format_args!("unexpected {ch}")
                        ));
                        continue 'parsing
                    }
                    Err(TokenizerError::Unterminated { name }) => {
                        errors.push(Rich::custom(
                            span,
                            format_args!("unterminated {name}")
                        ));
                        continue 'parsing
                    }
                };

                paste::paste! {
                    match token {
                        $(
                        $token::[<L $paren_name>] => {
                            paren_stack.push(ParenStackEntry {
                                span_start: span,
                                paren_kind: ParenKind::$paren_name,
                            });
                        }
                        $token::[<R $paren_name>] => match paren_stack.pop() {
                            Some(ParenStackEntry { span_start: _, paren_kind: ParenKind::$paren_name }) => {},
                            Some(ParenStackEntry { span_start, paren_kind }) => {
                                let (span_start, message) = (
                                    span_start,
                                    alloc::format!(concat!("mismatched closing delimiter; expected ", "paren", " {}"), paren_kind.name())
                                );
                                errors.push(Rich::custom(
                                    merge_span_back(span_start),
                                    message
                                ));
                                continue 'parsing
                            }
                            None => {
                                errors.push(Rich::custom(
                                    span,
                                    "unbalanced paren"
                                ));
                                continue 'parsing
                            }
                        },)*
                        _ => {}
                    }
                };

                tokens.push(Spanned {
                    span,
                    value: token
                })
            }

            if !errors.is_empty() {
                return Err(crate::compile::error::Error::syntax_error(
                    source,
                    errors
                ))
            }

            Ok(tokens)
        }
    };
}

// TODO: struct token

make_token! {
    enum Token {
        { KW: Let   = "let"   }
        { KW: Fn    = "fn"    }
        { KW: Pub   = "pub"   }
        { KW: Const = "const" }
        { KW: If    = "if"    }
        { KW: Else  = "else"  }
        { KW: Loop  = "loop"  }
        { KW: While = "while" }
        { KW: Use   = "use"   }
        { KW: For   = "for"   }
        { KW: True  = "true"  }
        { KW: False = "false" }
        { KW: Wildcard = "_"  }

        { paren: Paren, "paren"     = ['(', ')'] }
        { paren: Bracket, "curly bracket" = ['{', '}'] }
        { paren: SquareBracket, "square bracket"  = ['[', ']'] }

        // Control
        { Arrow = ['-', ">"] }
        { Comma = [','] }
        { Range = ['.', "."] }
        { Dot = ['.'] }
        { DoubleColon = [':', ":"] }
        { Colon = [':'] }
        { SemiColon = [';'] }

        // Operators:

        // Cmp
        { Equality  = ['=', "="] }
        { Assign    = ['='] }


        { Shl = ['<', "<"] }

        { Le = ['<', "="] }
        { Lt = ['<']  }

        { Shr = ['>', ">"] }

        { Ge = ['>', "="] }
        { Gt = ['>']  }

        { Ne = ['!', "="] }
        { Not = ['!'] }

        { LogicalOr = ['|', "|"] }
        { Or = ['|'] }

        { LogicalAnd = ['&', "&"] }
        { And = ['&'] }

        { Caret = ['^'] }

        // Arithmetic
        { EMod = ['%', "%"] }
        { EDiv = ['/', "%"] }

        { Plus = ['+'] }
        { AddAssign = ['+', "="] }
        { Minus = ['-'] }
        { SubAssign = ['-', "="] }
        { Star = ['*'] }
        { MulAssign = ['*', "="] }
        { Slash = ['/'] }
        { DivAssign = ['/', "="] }
        { Percent = ['%'] }
        { RemAssign = ['%', "="] }
    }
}

#[derive(Copy, Clone)]
pub struct TokenView<'src> {
    source: &'src Source<'src>,
    token: Spanned<Token>,
}
impl<'src> TokenView<'src> {
    pub fn as_token(&self) -> Token {
        self.token.value
    }

    pub fn span(&self) -> SimpleSpan {
        self.token.span
    }

    pub fn view(&self) -> &'src str {
        &self.source.contents()[self.span().into_range()]
    }
}
impl<'src> Debug for TokenView<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_struct(stringify!(TokenView))
            .field("span", &self.span())
            .field("token", &self.as_token())
            .field("view", &self.view())
            .finish()
    }
}

pub struct TokenizedSource<'a> {
    source: Source<'a>,
    tokens: Vec<Spanned<Token>>,
}

impl<'a> TokenizedSource<'a> {
    pub(crate) fn new(source: Source<'a>) -> crate::compile::error::Result<'a, Self> {
        Ok(Self {
            source: source.clone(),
            tokens: normalize_tokens(source.clone(), tokenize(source.contents()))?,
        })
    }

    pub fn source(&self) -> &Source<'a> {
        &self.source
    }

    pub fn tokens<'b>(
        &'b self,
    ) -> impl Iterator<Item = TokenView<'b>> + DoubleEndedIterator + ExactSizeIterator + use<'a, 'b>
    {
        let source = &self.source;
        self.tokens
            .iter()
            .map(move |&token| TokenView { source, token })
    }

    pub(crate) fn tokens_slice(&self) -> &[Spanned<Token>] {
        &self.tokens
    }
}
