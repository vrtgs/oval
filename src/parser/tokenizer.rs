use chumsky::error::Rich;
use chumsky::input::InputRef;
use chumsky::{extra, IterParser, ParseResult, Parser};
use chumsky::prelude::{choice, just};
use chumsky::span::SimpleSpan;
use chumsky::text::ident;
use chumsky::util::{Maybe, MaybeRef};

type TokenizerExtra<'a> = extra::Err<Rich<'a, char>>;

trait TokenImpl<'a>: Sized {
    fn parser() -> impl Parser<'a, &'a str, Self, TokenizerExtra<'a>>;
}


macro_rules! custom_err {
    (
        span: $span:expr,
        expected: $expected: expr,
        found: $found: expr $(,)?
    ) => {
        return Err(chumsky::error::LabelError::<&'a str, _>::expected_found(
            $expected,
            ($found).map(MaybeRef::<'static, char>::from),
            $span
        ))
    };
}

#[derive(Copy, Clone)]
pub struct QuotedLiteral<const QUOTE: char>;

fn parse_quoted<'a>(quote: char) -> impl Parser<'a, &'a str, (), TokenizerExtra<'a>> {
    chumsky::primitive::custom(move |input| {
        let _string_start = input.cursor();

        macro_rules! no_quote {
            ($found: expr) => {
                custom_err!(
                    span: input.span_since(&_string_start),
                    expected: [quote],
                    found: $found as Option<char>
                )
            };
        }

        match input.next() {
            Some(chr) if chr == quote => (),
            found => no_quote!(found)
        };

        loop {
            let Some(char) = input.next() else {
                no_quote!(None)
            };

            if char == quote {
                break 
            }
            
            if char == '\\' {
                // the next value is escaped
                // so even if it it the same quote discard
                let Some(_) = input.next() else {
                    no_quote!(None)
                };
            }
        };
        
        Ok(())
    })
}


impl<'a, const QUOTE: char> TokenImpl<'a> for QuotedLiteral<QUOTE> {
    fn parser() -> impl Parser<'a, &'a str, Self, TokenizerExtra<'a>> {
        const { assert!(QUOTE == '"' || QUOTE == '\'', "invalid quote specified") }
        parse_quoted(QUOTE).to(QuotedLiteral)
    }
}

#[derive(Copy, Clone)]
pub enum Base {
    Binary = 2,
    Octal = 8,
    Decimal = 10,
    Hex = 16
}

#[derive(Copy, Clone)]
pub struct Number;

impl<'a> TokenImpl<'a> for Number {
    fn parser() -> impl Parser<'a, &'a str, Self, TokenizerExtra<'a>> {
        chumsky::primitive::custom(|input: &mut InputRef<&'a str, _>| {
            let num_start = input.cursor();
            
            let mut base = Base::Decimal;
            match input.next() {
                Some('0') => 'peek_base: {
                    base = match input.peek() { 
                        Some('b') => Base::Binary,
                        Some('o') => Base::Octal,
                        Some('x') => Base::Hex,
                        _ => break 'peek_base
                    };
                    input.next();
                }
                Some('1'..='9') => (),
                found => {
                    custom_err!(
                        span: input.span_since(&num_start),
                        expected: std::array::from_fn::<_, 10, _>(|i| (b'0' + i as u8) as char),
                        found: found.map(Maybe::Val),
                    )
                }
            }

            while input.peek().is_some_and(move |c: char| c == '_' || c.is_digit(base as u32)) {
                input.next();
            }

            while input.peek().is_some_and(move |c: char| c == '_' || c.is_ascii_alphanumeric()) {
                input.next();
            }

            Ok(Number)
        })
    }
}

macro_rules! make_token {
    (enum $enum:ident {
        $({$($tt:tt)*})*
    }) => {
        make_token! {
            $enum,
            acc: { $({$($tt)*})* }
            type_based: {}
            keywords: {}
            string_based: {}
        }
    };
    
    (
        $enum:ident,
        acc: { { KW: $new_kw_name:ident = $new_kw:literal } $($rest:tt)* }
        type_based: { $($typed_name:ident($type:ty)),* }
        keywords: { $($kw_name:ident = $kw:literal),* }
        string_based: { $($str_name:ident = $str:literal),* }
    ) => {
        make_token! {
            $enum,
            acc: { $($rest)* }
            type_based: {  $( $typed_name($type)),* }
            keywords: { $($kw_name = $kw,)* $new_kw_name = $new_kw }
            string_based: { $($str_name = $str),* }
        }
    };
    
    (
        $enum:ident,
        acc: { { $new_str_name:ident = $new_str:literal } $($rest:tt)* }
        type_based: { $($typed_name:ident($type:ty)),* }
        keywords: { $($kw_name:ident = $kw:literal),* }
        string_based: { $($str_name:ident = $str:literal),* }
    ) => {
        make_token! {
            $enum,
            acc: { $($rest)* }
            type_based: {  $( $typed_name($type)),* }
            keywords: { $($kw_name = $kw),* }
            string_based: { $($str_name = $str,)* $new_str_name = $new_str }
        }
    };
    
    (
        $enum:ident,
        acc: { { $new_typed_name:ident($new_type:ty)} $($rest:tt)* }
        type_based: { $($typed_name:ident($type:ty)),* }
        keywords: { $($kw_name:ident = $kw:literal),* }
        string_based: { $($str_name:ident = $str:literal),* }
    ) => {
        make_token! {
            $enum,
            acc: { $($rest)* }
            type_based: {  $( $typed_name($type), )* $new_typed_name($new_type) }
            keywords: { $($kw_name = $kw),* }
            string_based: { $($str_name = $str),* }
        }
    };
    
    (
        $enum:ident,
        acc: {}
        type_based: { $($typed_name:ident($type:ty)),* }
        keywords: { $($kw_name:ident = $kw:literal),* }
        string_based: { $($str_name:ident = $str:literal),* }
    ) => {
        #[derive(Copy, Clone, Debug, PartialEq)]
        pub enum $enum {
            Ident,
            $($kw_name,)*
            $($typed_name,)*
            $($str_name),*
        }
        
        impl<'a> TokenImpl<'a> for $enum { 
            fn parser() -> impl Parser<'a, &'a str, Self, TokenizerExtra<'a>> {
                chumsky::text::whitespace().ignore_then(choice((
                    ident().map(|str| match str {
                        $($kw => Self::$kw_name,)*
                        _ => $enum::Ident
                    }),
                    $(<$type as TokenImpl<'a>>::parser().map(|_| Self::$typed_name),)*
                    choice([$(just($str).to(Self::$str_name)),*]),
                )))
            }
        }
        
    };
}

make_token! {
    enum TokenInner {
        { KW: Let   = "let"  }
        { KW: Ref   = "ref"  }
        { KW: Mut   = "mut"  }
        { KW: Fun   = "fun"  }
        { KW: If    = "if"   }
        { KW: Else  = "else" }
        { KW: Loop  = "loop" }
        { KW: Where = "Where" }
        
        { StringLiteral(QuotedLiteral<'"'>) }
        { CharLiteral(QuotedLiteral<'\''>) }
        { NumberLiteral(Number) }
        
        // Control
        { Arrow = "->" }
        { Comma = "," }
        { Colon = ":" }
        { SemiColon = ";" }
        
        { LParen   = "(" }
        { RParen   = ")" }
        
        { LBracket = "{" }
        { RBracket = "}" }
        
        { LBrace   = "[" }
        { RBrace   = "]" }
        
        
        // Operators:
        
        // Cmp
        { Equality = "==" }
        { Assign   = "=" }
        
        { Le = "<=" }
        { Lt = "<"  }
        { Ge = ">=" }
        { Gt = ">"  }
        
        // Arithmetic
        { EMod = "%%" }
        { EDiv = "/%" }
        
        { Add = "+" }
        { Sub = "-" }
        { Mul = "*" }
        { Div = "/" }
        { Mod = "%" }
        
        // Deref
        { Deref = "*" }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Token {
    inner: TokenInner,
    span: SimpleSpan,
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl Token {
    pub const fn from_inner(inner: TokenInner) -> Token {
        Token {
            inner,
            span: SimpleSpan {
                start: 0,
                end: 0,
                context: ()
            }
        }
    }
    
    pub fn span(&self) -> SimpleSpan {
        self.span
    }
    
    pub fn inner(&self) -> &TokenInner {
        &self.inner
    }
}

pub fn tokenize(input: &str) -> ParseResult<Vec<Token>, Rich<'_, char>> {
    let parser = TokenInner::parser().map_with(|inner, extra| Token {
        span: extra.span(),
        inner
    });
    
    parser.repeated().collect().parse(input)
}