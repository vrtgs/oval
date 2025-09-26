use crate::interner::Symbol;
use crate::parser::{AstParse, InputTape, OvalParser, ParserData, ParserState};
use crate::spanned::{spanned_struct, Span, Spanned};
use chumsky::extra::SimpleState;
use chumsky::Parser;
use core::fmt::{Debug, Formatter};
use core::iter::FusedIterator;
use core::str::Chars;
use thiserror::Error;
use crate::parser::static_parser;

macro_rules! impl_token_ty {
    ($name: ident = $str: tt) => {
        #[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
        pub struct $name(Span);

        impl Debug for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                f.write_str(stringify!($name))
            }
        }

        impl $name {
            pub fn try_from_token(token: Token) -> Option<Self> {
                let TokenKind::$name = token.kind else {
                    return None;
                };

                Some(Self(token.span))
            }

            pub fn from_token(token: Token) -> Self {
                Self::try_from_token(token).expect({
                    concat!(
                        stringify!($name),
                        "::from_token should be called with the correct token"
                    )
                })
            }
        }

        impl Spanned for $name {
            fn span(&self) -> Span {
                self.0
            }
        }

        impl AstParse for $name {
            fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>()
            -> impl OvalParser<'src, I, Self, E> {
                static_parser! {
                    chumsky::primitive::just(TokenKind::$name)
                        .map_with(|_, extra| $name(extra.span()))
                }
            }
        }
    };
}

macro_rules! make_tokens {
    (
        Keywords {
            $($kw_name: ident = $kw_str: tt;)+
        }

        Delimiter {
            $($paren_name: ident | $paren_name_lower: ident = [$l_paren: tt, $r_paren: tt];)+
        }

        PlainToken {
            $($plain_name: ident = $plain_token_str: tt;)+
        }
    ) => {
        const _: () = {
            $(assert!($kw_str.is_ascii(), concat!("non ascii keyword `", $kw_str , "`"));)+
            $(
            let kw_str: &str = $kw_str;
            let mut kw = kw_str.as_bytes();

            assert!(
                !kw[0].is_ascii_digit(),
                concat!("keyword `", $kw_str , "` can't start with a digit")
            );

            while let [byte, rest @ ..] = kw {
                kw = rest;
                let byte = *byte;
                assert!(
                    byte.is_ascii_alphanumeric() || byte == b'_',
                    concat!("keyword `", $kw_str , "` is not a valid identifier")
                )
            }
            )+
        };

        const _: () = {
            $(

            assert!(
                $plain_token_str.is_ascii(),
                concat!("non ascii token `", $plain_token_str , "`")
            );

            let mut token = $plain_token_str.as_bytes();

            while let [byte, rest @ ..] = token {
                token = rest;
                let byte = *byte;
                assert!(
                    !byte.is_ascii_alphanumeric() && !byte.is_ascii_whitespace(),
                    concat!("token `", $plain_token_str , "` must contain symbols only")
                )
            }

            )+
        };

        $(impl_token_ty! { $kw_name = $kw_str })+
        $(impl_token_ty! { $plain_name = $plain_token_str })+

        $(
        #[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
        pub struct $paren_name<T>(pub T, Span);

        impl<T> $paren_name<T> {
            pub fn new(item: T, span: Span) -> $paren_name<T> {
                $paren_name(item, span)
            }

            pub fn map<U>(self, mapper: impl FnOnce(T) -> U) -> $paren_name<U> {
                let $paren_name(item, span) = self;
                $paren_name(mapper(item), span)
            }
        }

        impl<T> Spanned for $paren_name<T> {
            fn span(&self) -> Span {
                self.1
            }
        }


        )+



        #[macro_export]
        macro_rules! TokenTy {
            $(($kw_str) => {$crate::tokens::$kw_name};)+
            $(($plain_token_str) => { $crate::tokens::$plain_name};)+
            $(($l_paren, $__make_tokens_TY__: ty, $r_paren) => {
                $crate::tokens::$paren_name<$__make_tokens_TY__>
            };)+
        }

        pub use TokenTy;

        #[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
        pub enum Literal {
            String,
            Char,
            Integer,
            Bool(bool),
            Float
        }

        paste::paste! {
            #[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
            pub enum TokenKind {
                Ident,
                Literal(Literal),
                $(
                [<R $paren_name>],
                [<L $paren_name>],
                )+
                $($kw_name,)+
                $($plain_name,)+
            }

            impl TokenKind {
                pub(crate) fn name(self) -> &'static str {
                    match self {
                        Self::Ident => "identifier",
                        Self::Literal(_) => "literal",
                        $(
                        Self::[<R $paren_name>] => concat!($r_paren, ""),
                        Self::[<L $paren_name>] => concat!($l_paren, ""),
                        )+
                        $(Self::$kw_name => $kw_str,)+
                        $(Self::$plain_name => $plain_token_str,)+
                    }
                }
            }
            impl core::fmt::Display for TokenKind {
                fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                    f.write_str(match self {
                        Self::Ident => "identifier",
                        Self::Literal(_) => "literal",
                        $(
                        Self::[<R $paren_name>] => concat!(r#"""#, $r_paren, r#"""#),
                        Self::[<L $paren_name>] => concat!(r#"""#, $l_paren, r#"""#),
                        )+
                        $(Self::$kw_name => $kw_str,)+
                        $(Self::$plain_name => stringify!($plain_token_str),)+
                    })
                }
            }
        }




        #[derive(Debug, Error, Hash, Eq, PartialEq)]
        pub enum TokenizerErrorKind {
            #[error("unknown start of token {char}")]
            UnknownChar {
                char: char,
                start: usize
            },
            #[error("expected one of {expected:?} found `{found:?}`")]
            UnexpectedChar {
                found: Option<char>,
                expected: &'static [char],
                start: usize
            },
        }

        impl Spanned for TokenizerErrorKind {
            fn span(&self) -> Span {
                match *self {
                    Self::UnknownChar { char, start } => {
                        Span::new(start, start + char.len_utf8())
                    }
                    Self::UnexpectedChar { found, start, .. } => {
                        Span::new(start, start + found.map_or(0, char::len_utf8))
                    }
                }
            }
        }

        #[derive(Debug, Error)]
        #[error(transparent)]
        pub struct TokenizerError(pub(crate) TokenizerErrorKind);

        impl Spanned for TokenizerError {
            fn span(&self) -> Span {
                self.0.span()
            }
        }


        #[derive(Debug, Clone)]
        pub(crate) struct Tokenizer<'a> {
            chars: Chars<'a>,
            str_len: usize
        }

        impl<'a> Tokenizer<'a> {
            pub fn new(str: &'a str) -> Self {
                Self {
                    chars: str.chars(),
                    str_len: str.len()
                }
            }
        }

        impl<'a> Iterator for Tokenizer<'a> {
            type Item = Result<Token, TokenizerError>;

            fn next(&mut self) -> Option<Self::Item> {
                'tokenizing:
                loop {
                    let token_start_str = self.chars.as_str().trim_ascii_start();
                    self.chars = token_start_str.chars();
                    let first_char = self.chars.next()?;

                    let token_start = self.str_len - token_start_str.len();

                    macro_rules! eat {
                        ($__make_tokens_pattern__: pat) => {('ret: {
                            let mut cloned = self.chars.clone();
                            if let Some($__make_tokens_pattern__) = cloned.next() {
                                self.chars = cloned;
                                break 'ret true
                            }

                            false
                        })};
                    }

                    macro_rules! eat_while {
                        ($__make_tokens_pattern__: pat) => {
                            while eat!($__make_tokens_pattern__) {}
                        };
                    }

                    paste::paste! {
                        $(
                        #[expect(non_upper_case_globals)]
                        const [<$plain_name _PATTENRS>]: (char, &str) = {
                            let (start, suffix) = ($plain_token_str).as_bytes().split_at(1);
                            assert!(start.len() == 1);
                            let start = start[0];
                            assert!(start.is_ascii());
                            let start = start as char;
                            let suffix = match str::from_utf8(suffix) {
                                Ok(str) => str,
                                Err(_) => panic!(
                                    "all tokens are ascii; so this should always work"
                                )
                            };

                            (start, suffix)
                        };

                        #[expect(non_upper_case_globals)]
                        const [<$plain_name _START>]: char = [<$plain_name _PATTENRS>].0;

                        #[expect(non_upper_case_globals)]
                        const [<$plain_name _SUFFIX>]: &str = [<$plain_name _PATTENRS>].1;
                        )+

                        const ALL_PLAIN_TOKENS_PATTERNS: &[((char, &str), TokenKind)] = &[
                            $(([<$plain_name _PATTENRS>], TokenKind::$plain_name)),+
                        ];

                        let token = 'result: {
                            let token = match first_char {
                                'a'..='z' | 'A'..='Z' | '_' => {
                                    eat_while!('a'..='z' | 'A'..='Z' | '0'..='9' | '_');

                                    let end_relative = {
                                        token_start_str.len() - self.chars.as_str().len()
                                    };

                                    let ident = &token_start_str[..end_relative];

                                    #[deny(unreachable_patterns)]
                                    match ident {
                                        "true" => TokenKind::Literal(Literal::Bool(true)),
                                        "false" => TokenKind::Literal(Literal::Bool(false)),
                                        $($kw_str => TokenKind::$kw_name,)+
                                        _ => TokenKind::Ident
                                    }
                                },
                                '0'..='9' => {
                                    eat_while!('0'..='9' | '_');
                                    // e is not allowed to start the suffix
                                    #[allow(non_contiguous_range_endpoints)]
                                    if eat!('a'..'e' | 'f'..='z' | 'A'..'E' | 'F'..='Z') {
                                        eat_while!('a'..='z' | 'A'..='Z' | '0'..='9' | '_');
                                    }

                                    TokenKind::Literal(Literal::Integer)
                                }
                                '/' if eat!('/') => {
                                    let str = self.chars.as_str();
                                    let str = str.split_once('\n').map_or(
                                        "",
                                        |(_comment, tail)| tail
                                    );
                                    self.chars = str.chars();
                                    continue 'tokenizing
                                }
                                $(
                                    $l_paren => TokenKind::[<L $paren_name>],
                                    $r_paren => TokenKind::[<R $paren_name>],
                                )+

                                $(
                                #[expect(non_upper_case_globals)]
                                #[allow(unreachable_patterns)]
                                [<$plain_name _START>] => 'plain_ret: {
                                    const START: char = [<$plain_name _START>];
                                    const SUFFIX: &str = [<$plain_name _SUFFIX>];

                                    const DUPLICATES_COUNT: usize = {
                                        let mut count = 0;
                                        let mut iter = ALL_PLAIN_TOKENS_PATTERNS;
                                        while let [((start, _), _), rest @ ..] = iter {
                                            iter = rest;
                                            if *start == START {
                                                count += 1;
                                            }
                                        }

                                        count - 1
                                    };

                                    const fn const_str_eq(a: &str, b: &str) -> bool {
                                        if a.len() != b.len() {
                                            return false
                                        }

                                        let mut a = a.as_bytes();
                                        let mut b = b.as_bytes();
                                        while let ([rest_a @ .., byte_a], [rest_b @ .., byte_b]) = (a, b) {
                                            if *byte_a != *byte_b {
                                                return false;
                                            }

                                            a = rest_a;
                                            b = rest_b;
                                        }
                                        true
                                    }

                                    const DUPLICATES_SUFFIX: [(&str, TokenKind); DUPLICATES_COUNT] = 'ret: {
                                        let mut dupes = [("", TokenKind::$plain_name); DUPLICATES_COUNT];
                                        if DUPLICATES_COUNT == 0 {
                                            break 'ret dupes
                                        }

                                        let mut dup_count = 0;
                                        let mut found_self = false;
                                        let mut iter = ALL_PLAIN_TOKENS_PATTERNS;

                                        'finding_duplicates:
                                        while let [((start, suffix), token), rest @ ..] = iter {
                                            iter = rest;
                                            if *start != START {
                                                continue 'finding_duplicates
                                            }

                                            if const_str_eq(suffix, SUFFIX) {
                                                match found_self {
                                                    true => panic!(concat!(
                                                        "duplicate token definition `",$plain_token_str,"`"
                                                    )),
                                                    false => {
                                                        found_self = true;
                                                        continue 'finding_duplicates
                                                    }
                                                }
                                            }

                                            dupes[dup_count] = (suffix, *token);
                                            dup_count += 1;
                                        }

                                        assert!(found_self);
                                        assert!(dup_count == DUPLICATES_COUNT);

                                        dupes
                                    };

                                    // if no duplicates this is trivial

                                    if const { DUPLICATES_COUNT == 0 && SUFFIX.is_empty() } {
                                        break 'plain_ret TokenKind::$plain_name
                                    }


                                    const COUNT_TOTAL: usize = DUPLICATES_COUNT + 1;

                                    // surprisingly these are all unique, since well this computation
                                    // runs on all duplicate starts
                                    // and all duplicate starts check for duplicate suffixes
                                    const SORTED_SUFFIXES: [(&str, TokenKind); COUNT_TOTAL] = {
                                        let mut combined = [(SUFFIX, TokenKind::$plain_name); DUPLICATES_COUNT + 1];

                                        let mut i = 0;
                                        while i < DUPLICATES_COUNT {
                                            combined[i] = DUPLICATES_SUFFIX[i];
                                            i += 1;
                                        }

                                        // Insertion sort by suffix length (descending)
                                        let mut idx = 1;
                                        while idx < combined.len() {
                                            let mut j = idx;
                                            while j > 0 && combined[j - 1].0.len() < combined[j].0.len() {
                                                combined.swap(j - 1, j);
                                                j -= 1;
                                            }
                                            idx += 1;
                                        }

                                        combined
                                    };

                                    const EXPECTED_FULL: ([char; COUNT_TOTAL], usize) = {
                                        let mut suffixes = ['\0'; COUNT_TOTAL];
                                        let mut inserted = 0;
                                        let mut i = 0;
                                        while i < COUNT_TOTAL {
                                            let suffix = SORTED_SUFFIXES[i].0;
                                            match *suffix.as_bytes() {
                                                [] => assert!(i == COUNT_TOTAL - 1),
                                                [first, ..] => {
                                                    assert!(first.is_ascii());
                                                    suffixes[inserted] = first as char;
                                                    inserted += 1;
                                                }
                                            }

                                            i += 1;
                                        }

                                        (suffixes, inserted)
                                    };

                                    const EXPECTED: &'static [char] = {
                                        let (array, len) = &EXPECTED_FULL;
                                        // const hack since array[..len] is unstable
                                        let (expected, _empty_tail) = array.split_at(*len);
                                        expected
                                    };

                                    macro_rules! run_on {
                                        ($__SUFFIX_EXPR__: expr) => {'find_block: {
                                            for (suffix, tk) in const { $__SUFFIX_EXPR__ } {
                                                match suffix.as_bytes() {
                                                    &[single] => {
                                                        let mut clone = self.chars.clone();
                                                        if Some(single as char) == clone.next() {
                                                            self.chars = clone;
                                                            break 'find_block Some(tk)
                                                        }
                                                    }
                                                    _ => {
                                                        let Some(stripped) = self.chars.as_str().strip_prefix(suffix) else {
                                                            continue
                                                        };

                                                        self.chars = stripped.chars();
                                                        break 'find_block Some(tk)
                                                    }
                                                }
                                            }

                                            None
                                        }}
                                    }

                                    if const { SORTED_SUFFIXES.last().unwrap().0.is_empty() } {
                                        const LAST_IS_EMPTY_DATA: ([(&str, TokenKind); DUPLICATES_COUNT], TokenKind) = {
                                            let [prefix @ .., (_, last_kind)] = SORTED_SUFFIXES;
                                            (prefix, last_kind)
                                        };

                                        // if we have an empty suffix; that means we never emit
                                        // UnexpectedChar
                                        run_on!(LAST_IS_EMPTY_DATA.0)
                                            .unwrap_or(const { LAST_IS_EMPTY_DATA.1 })
                                    } else {
                                        let Some(tk) = run_on!(SORTED_SUFFIXES) else {
                                            let found = self.chars.next();
                                            break 'result Err(TokenizerErrorKind::UnexpectedChar {
                                                found,
                                                expected: EXPECTED,
                                                start: token_start
                                            })
                                        };

                                        tk
                                    }
                                }
                                )+
                                unknown => {
                                    break 'result Err(TokenizerErrorKind::UnknownChar {
                                        char: unknown,
                                        start: token_start
                                    })
                                }
                            };


                            let token_end = self.str_len - self.chars.as_str().len();
                            Ok(Token {
                                span: Span::new(token_start, token_end),
                                kind: token
                            })
                        };

                        break Some(token.map_err(TokenizerError))
                    }
                }
            }
        }

        impl FusedIterator for Tokenizer<'_> {}

        impl AstParse for Ident {
            fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>() -> impl OvalParser<'src, I, Self, E> {
                static_parser! {
                    chumsky::primitive::just(TokenKind::Ident).map_with(|_, extra| {
                        let span: Span = extra.span();
                        let mut state: &mut SimpleState<ParserState<E::Error>> = extra.state();
                        let state: &mut ParserState<E::Error> = &mut state;
                        let symbol = state.interner.get_or_intern(&state.text[span.into_range()]);


                        Ident {
                            span,
                            symbol
                        }
                    })
                }
            }
        }
    };
}

make_tokens! {
    Keywords {
        Fn = "fn";
        Const = "const";
        Let = "let";
        Mut = "mut";
        Loop = "loop";
        If = "if";
        Else = "else";
        Break = "break";
        Continue = "continue";
        Return = "return";
        Pub = "pub";
        Extern = "extern";
        As = "as";
    }

    Delimiter {
        Paren | paren = ['(', ')'];
        CurlyBrace | curly_brace = ['{', '}'];
        SquareBracket | square_bracket = ['[', ']'];
    }

    PlainToken {
        Colon = ":";
        Semicolon = ";";
        DoubleColon = "::";
        Comma = ",";
        Arrow = "->";

        Equals = "=";

        Not = "!";
        Minus = "-";
        Plus = "+";
        Star = "*";
        Slash = "/";
        Percent = "%";

        // comparisons
        LessThan = "<";
        LessthanOrEqual = "<=";
        GreaterThan = ">";
        GreaterThanOrEqual = ">=";
        
        // equality
        IsEquality = "==";
        IsNotEqual = "!=";
    }
}

const _: () = assert!(size_of::<TokenKind>() <= 1);

#[derive(Debug, Copy, Clone)]
pub struct Ident {
    pub(crate) span: Span,
    pub(crate) symbol: Symbol,
}

impl Ident {
    pub fn symbol(&self) -> Symbol {
        self.symbol
    }
}

spanned_struct!(Ident);

#[derive(Debug, Copy, Clone)]
pub struct Token {
    pub span: Span,
    pub kind: TokenKind,
}

impl Token {
    pub fn kind(&self) -> TokenKind {
        self.kind
    }
}

spanned_struct!(Token);
