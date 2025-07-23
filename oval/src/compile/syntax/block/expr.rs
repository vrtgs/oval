use crate::compile::interner::{Interner, Symbol};
use crate::compile::syntax::block::Block;
use crate::compile::syntax::{
    OvalParserExt, Parser, ParserExtra, SealedParseAst, recursive_parser,
};
use crate::compile::tokenizer::Token;
use crate::symbol::Path;
use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use chumsky::IterParser;
use chumsky::error::Rich;
use chumsky::input::{Emitter, Input, MapExtra};
use chumsky::pratt::{infix, left, postfix, prefix, right};
use chumsky::prelude::{SimpleSpan, just, recursive};
use chumsky::primitive::choice;

#[derive(Debug, Copy, Clone)]
pub enum AssignOp {
    /// `=`
    Simple,
    /// `+=`
    Add,
}

#[derive(Debug, Copy, Clone)]
pub enum UnOp {
    /// The `*` operator for dereferencing
    Deref,
    /// The `&` operator for referencing
    Ref,
    /// The `!` operator for logical inversion
    Not,
    /// The `-` operator for negation
    Neg,
}

impl UnOp {
    const BINDING_POWER: u16 = 10;
}

macro_rules! declare_bin_ops {
    (
        enum $name: ident {
            $($(#[$($doc:tt)*])* $variant: ident),+ $(,)?
        }
    ) => {
        #[derive(Debug, Copy, Clone)]
        pub enum $name {
            $(
            $(#[$($doc)*])*
            $variant
            ),+
        }

        impl $name {
            const VARIANTS: &[Self] = &[$(Self::$variant),+];
        }
    };
}

declare_bin_ops! {
    enum BinOp {
        /// The `+` operator (addition)
        Add,
        /// The `-` operator (subtraction)
        Sub,
        /// The `*` operator (multiplication)
        Mul,
        /// The `/` operator (division)
        Div,
        /// The `/%` operator (euclidean division)
        EDiv,
        /// The `%` operator (remainder)
        Rem,
        /// The `%%` operator (euclidean modulus)
        EMod,
        /// The `&&` operator (logical and)
        LogicalAnd,
        /// The `||` operator (logical or)
        LogicalOr,
        /// The `^` operator (bitwise xor)
        BitXor,
        /// The `&` operator (bitwise and)
        BitAnd,
        /// The `|` operator (bitwise or)
        BitOr,
        /// The `<<` operator (shift left)
        Shl,
        /// The `>>` operator (shift right)
        Shr,
        /// The `==` operator (equality)
        Eq,
        /// The `<` operator (less than)
        Lt,
        /// The `<=` operator (less than or equal to)
        Le,
        /// The `!=` operator (not equal to)
        Ne,
        /// The `>=` operator (greater than or equal to)
        Ge,
        /// The `>` operator (greater than)
        Gt,
    }
}

impl BinOp {
    const MIN_BINDING_POWER: u16 = 2;
    const MAX_BINDING_POWER: u16 = 10;

    const fn binding_power(self) -> u16 {
        let pow = match self {
            BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::EMod | BinOp::EDiv => 10,
            BinOp::Add | BinOp::Sub => 9,
            BinOp::Shl | BinOp::Shr => 8,
            BinOp::BitAnd => 7,
            BinOp::BitXor => 6,
            BinOp::BitOr => 5,
            BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt => 4,
            BinOp::LogicalAnd => 3,
            BinOp::LogicalOr => 2,
        };

        assert!(Self::MIN_BINDING_POWER <= pow && pow <= Self::MAX_BINDING_POWER);

        pow
    }
}

#[derive(Debug, Copy, Clone)]
pub enum LiteralExpr {
    String(Symbol),
    Char(char),
    Num(SimpleSpan),
    Bool(bool),
}

fn quoted_parser<'c, 'a: 'state, 'state, I: Input<'a, Token = Token, Span = SimpleSpan>>(
    extra: &'state mut MapExtra<'a, '_, I, ParserExtra<'a>>,
    emitter: &mut Emitter<Rich<Token>>,
) -> (Cow<'state, str>, &'state mut Interner) {
    let span = extra.span();
    let (source, interner) = &mut extra.state().0;
    let compiler = &mut **interner;
    let source = *source;

    struct LiteralBuilder {
        last_copy_end: usize,
        literal: String,
    }

    let mut builder = const {
        LiteralBuilder {
            last_copy_end: 0,
            literal: String::new(),
        }
    };

    let range = span.into_range();
    // exclude the quotes from the string
    let quoted_slice = &source.contents()[range.start + 1..range.end - 1];
    let mut escape_sequences = quoted_slice.match_indices('\\').map(|(idx, _)| idx);

    // TODO: more specific spans
    'parsing_escapes: while let Some(idx) = escape_sequences.next() {
        let last_chunk = &quoted_slice[builder.last_copy_end..idx];
        let next = &quoted_slice[idx + 1..];
        let mut next_chars = next.chars();
        let escaped_char = match next_chars.next() {
            Some('\\') => {
                let _ = escape_sequences.next();
                '\\'
            }
            Some('u') => {
                let Some('{') = next_chars.next() else {
                    emitter.emit(Rich::custom(
                        span,
                        r"incorrect unicode escape sequence; format of unicode escape sequences is `\u{...}`"
                    ));
                    continue 'parsing_escapes;
                };
                let next_str = next_chars.as_str();
                let Some(end) = next_str.find('}') else {
                    emitter.emit(Rich::custom(span, "unterminated unicode escape"));
                    continue 'parsing_escapes;
                };

                let digits = &next_str[..end];

                if digits.len() > 6 {
                    emitter.emit(Rich::custom(
                        span,
                        "overlong unicode escape; must have at most 6 hex digits",
                    ));
                    continue 'parsing_escapes;
                }

                next_chars = next_str[end + 1..].chars();

                let number = digits
                    .as_bytes()
                    .iter()
                    .try_fold(0, |number: u32, &next: &u8| {
                        let next = next as char;
                        let Some(next_digit) = next.to_digit(16) else {
                            return Err(Rich::custom(
                                span,
                                format_args!("invalid character in unicode escape: `{next}`"),
                            ));
                        };
                        Ok(number * 16 + next_digit)
                    });

                let converted =
                    number.map(|num| (num <= char::MAX as u32).then_some(char::from_u32(num)));
                let res = match converted {
                    Ok(Some(Some(ch))) => Ok(ch),
                    Ok(Some(None)) => Err(Err("unicode escape must not be a surrogate")),
                    Ok(None) => Err(Err("unicode escape must be at most 10FFFF")),
                    Err(err) => Err(Ok(err)),
                };

                match res {
                    Ok(ch) => ch,
                    Err(err) => {
                        emitter.emit(err.unwrap_or_else(|msg| {
                            Rich::custom(
                                span,
                                format_args!("invalid unicode character escape; {msg}"),
                            )
                        }));

                        continue 'parsing_escapes;
                    }
                }
            }
            Some('n') => '\n',
            Some('r') => '\r',
            Some('t') => '\t',
            Some('0') => '\0',
            Some('x') => {
                let Some(number) = next_chars
                    .next()
                    .and_then(|ch| Some([ch, next_chars.next()?]))
                else {
                    emitter.emit(Rich::custom(span, "numeric character escape is too short"));
                    continue 'parsing_escapes;
                };

                let byte = number.into_iter().try_fold(0u8, |byte, next| {
                    let Some(digit) = next.to_digit(16) else {
                        return Err(Rich::custom(
                            span,
                            format_args!("invalid character in numeric character escape: `{next}`"),
                        ));
                    };

                    Ok(byte * 16 + digit as u8)
                });

                match byte {
                    Ok(byte) if byte.is_ascii() => byte as char,
                    Ok(byte) => {
                        emitter.emit(Rich::custom(
                            span,
                            format_args!("0x{byte:02x} out of range of hex escape"),
                        ));
                        continue 'parsing_escapes;
                    }
                    Err(err) => {
                        emitter.emit(err);
                        continue 'parsing_escapes;
                    }
                }
            }
            Some(chr) => {
                emitter.emit(Rich::custom(
                    span,
                    format_args!("unknown character escape `{chr}`"),
                ));
                continue 'parsing_escapes;
            }
            None => {
                emitter.emit(Rich::custom(span, "unterminated quoted literal"));
                continue 'parsing_escapes;
            }
        };

        builder
            .literal
            .reserve(last_chunk.len() + escaped_char.len_utf8());
        builder.literal += last_chunk;
        builder.literal.push(escaped_char);
        builder.last_copy_end = quoted_slice.len() - next_chars.as_str().len();
    }

    let str = match builder.last_copy_end {
        0 => Cow::Borrowed(quoted_slice),
        end => Cow::Owned(builder.literal + &quoted_slice[end..]),
    };

    (str, compiler)
}

impl SealedParseAst for LiteralExpr {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        let string_literal = just(Token::String).validate(|_, extra, emitter| {
            let (str, interner) = quoted_parser(extra, emitter);
            LiteralExpr::String(interner.intern(&str))
        });

        let char_literal = just(Token::Char).validate(|_, extra, emitter| {
            let (str, _) = quoted_parser(extra, emitter);
            let mut chars = str.chars();
            let char = match chars.next() {
                Some(ch) => {
                    if chars.next().is_some() {
                        emitter.emit(Rich::custom(
                            extra.span(),
                            "too many characters in char literal",
                        ));
                    }
                    ch
                }
                None => {
                    emitter.emit(Rich::custom(extra.span(), "Empty char literal"));
                    '\0'
                }
            };
            LiteralExpr::Char(char)
        });

        let number_parser =
            just(Token::Number).validate(|_, extra: &mut MapExtra<I, ParserExtra<'a>>, _| {
                LiteralExpr::Num(extra.span())
            });

        let bool_parser = choice([
            just(Token::True).to(LiteralExpr::Bool(true)),
            just(Token::False).to(LiteralExpr::Bool(false)),
        ]);

        choice((string_literal, char_literal, number_parser, bool_parser)).labelled("literal")
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Path(Path),
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    Parens(Box<Expr>),
    BinOp(BinOp, Box<(Expr, Expr)>),
    UnOp(UnOp, Box<Expr>),
    Literal(LiteralExpr),
    Block(Block),
    Call(Box<Expr>, Vec<Expr>),
    Loop(Block),
    While(Box<Expr>, Block),
    Ref {
        expr: Box<Expr>,
    },
    /// in the expr `x = b + z` `x` will be the first expr, `b + z` will be the second
    /// and the assign op will be `=`
    Assignment(AssignOp, Box<(Expr, Expr)>),
    // TODO: ForLoop, Closure
}

impl SealedParseAst for Expr {
    fn parser<'a, I: Input<'a, Token = Token, Span = SimpleSpan>>()
    -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        recursive(|expr_parser| {
            let block_parser = recursive_parser::<Block, I>();

            let parens_parser = expr_parser
                .clone()
                .separated_by(just(Token::Comma))
                .collect::<Vec<_>>()
                .then(just(Token::Comma).or_not().map(|x| x.is_some()))
                .in_parens()
                // TODO: tuple parsing with less code duplication
                .map(|(mut list, leading)| {
                    if !leading {
                        match <[_; 1]>::try_from(list) {
                            Ok([x]) => return Expr::Parens(Box::new(x)),
                            Err(fail) => list = fail,
                        }
                    }

                    Expr::Tuple(list)
                });

            let list_parser = expr_parser
                .clone()
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .collect::<Vec<Expr>>();

            let array = list_parser.clone().in_square_brackets().map(Expr::Array);

            let atom = choice((
                Path::parser().map(Expr::Path),
                LiteralExpr::parser().map(Expr::Literal),
                just(Token::Loop)
                    .ignore_then(block_parser.clone())
                    .map(Expr::Loop),
                just(Token::While)
                    .ignore_then(expr_parser.then(block_parser.clone()))
                    .map(|(expr, block)| Expr::While(Box::new(expr), block)),
                parens_parser,
                array,
                block_parser.clone().map(Expr::Block),
            ));

            macro_rules! make_bin_op_grouping {
                ($($bin_op:ident = $token: ident)|+) => {
                    // last but not least we have assignments
                    chumsky::pratt::infix(
                        left(const {
                            let binding_powers = [$(BinOp::$bin_op.binding_power()),+];
                            let [first, rest @ ..] = binding_powers;
                            let mut rest = rest.as_slice();

                            while let [additional, leftover @ ..] = rest {
                                assert!(*additional == first, "mismatched binding power");
                                rest = leftover;
                            }

                            let mut variants = BinOp::VARIANTS;
                            while let [variant, leftover @ ..] = variants {
                                if variant.binding_power() == first
                                    $(&& !matches!(variant, BinOp::$bin_op))+
                                {
                                    panic!("missing variants with similar binding power")
                                }

                                variants = leftover;
                            }

                            first
                        }),
                        choice([
                            $(just(Token::$token).to(BinOp::$bin_op)),+
                        ]),
                        |a, bin_op, c, _| {
                            Expr::BinOp(bin_op, Box::new((a, c)))
                        }
                    )
                };
            }

            let expr = atom.pratt((
                // function calls have greater binding power than anything
                postfix(
                    const { UnOp::BINDING_POWER + 1 },
                    list_parser.in_parens(),
                    |func, args, _| Expr::Call(Box::new(func), args),
                ),
                // then go the unary ops
                prefix(
                    UnOp::BINDING_POWER,
                    choice([
                        just(Token::Star).to(UnOp::Deref),
                        just(Token::And).to(UnOp::Ref),
                        just(Token::Not).to(UnOp::Not),
                        just(Token::Minus).to(UnOp::Neg),
                    ]),
                    |un_op, expr, _| Expr::UnOp(un_op, Box::new(expr)),
                ),
                // then the binary operators
                make_bin_op_grouping!(
                    Mul = Star | Div = Slash | Rem = Percent | EMod = EMod | EDiv = EDiv
                ),
                make_bin_op_grouping!(Add = Plus | Sub = Minus),
                make_bin_op_grouping!(Shr = Shr | Shl = Shl),
                make_bin_op_grouping!(BitAnd = And),
                make_bin_op_grouping!(BitOr = Or),
                make_bin_op_grouping!(BitXor = Caret),
                make_bin_op_grouping!(
                    Eq = Equality | Lt = Lt | Le = Le | Ne = Ne | Ge = Ge | Gt = Gt
                ),
                make_bin_op_grouping!(LogicalAnd = LogicalAnd),
                make_bin_op_grouping!(LogicalAnd = LogicalOr),
                // last but not least we have assignments
                infix(
                    right(const { BinOp::MIN_BINDING_POWER - 1 }),
                    choice([
                        just(Token::Assign).to(AssignOp::Simple),
                        just(Token::AddAssign).to(AssignOp::Add),
                    ]),
                    |a, assign, c, _| Expr::Assignment(assign, Box::new((a, c))),
                ),
            ));

            expr.labelled("expression")
        })
    }
}
