use chumsky::{select, IterParser};
use alloc::boxed::Box;
use alloc::vec::Vec;
use chumsky::input::ValueInput;
use chumsky::pratt::{right, left, postfix, prefix, infix};
use chumsky::prelude::{just, recursive, SimpleSpan};
use chumsky::primitive::choice;
use crate::compile::parser::block::Block;
use crate::compile::parser::{make_recursive_parsers, OvalParserExt, SealedParseAst, Parser, ParserExtra};
use crate::compile::tokenizer::Token;
use crate::symbol::Path;

#[derive(Debug, Copy, Clone)]
pub enum AssignOp {
    /// `=`
    Simple,
    /// `+=`
    Add
}

#[derive(Debug, Copy, Clone)]
pub enum UnOp {
    /// The `*` operator for dereferencing
    Deref,
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
pub enum LiteralKind {
    String(SimpleSpan),
    Num(SimpleSpan),
    Bool(bool)
}

#[derive(Debug, Clone)]
pub enum Expr {
    Path(Path),
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    Parens(Box<Expr>),
    BinOp(BinOp, Box<(Expr, Expr)>),
    UnOp(UnOp, Box<Expr>),
    Literal(LiteralKind),
    Block(Block),
    Call(Box<Expr>, Vec<Expr>),
    Loop(Block),
    While(Box<Expr>, Block),
    /// in the expr `x = b + z` `x` will be the first expr, `b + z` will be the second
    /// and the assign op will be `=`
    Assignment(AssignOp, Box<(Expr, Expr)>),

    // TODO: ForLoop
    // WISHLIST: Closure
}

impl Expr {
    pub(crate) fn make_parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>(
        block_parser: impl Parser<'a, I, Block, ParserExtra<'a>> + Clone + 'a,
    ) -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        recursive(|expr_parser| {
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
                            Err(fail) => list = fail
                        }
                    }

                    Expr::Tuple(list)
                });

            let list_parser = expr_parser
                .clone()
                .separated_by(just(Token::Comma))
                .allow_trailing()
                .collect::<Vec<Expr>>();

            let array = list_parser
                .clone()
                .in_square_brackets()
                .map(Expr::Array);

            let literal = select! {
                Token::String = e => LiteralKind::String(e.span()),
                Token::Float | Token::Int = e => LiteralKind::Num(e.span()),
                Token::True => LiteralKind::Bool(true),
                Token::False => LiteralKind::Bool(true),
            }.labelled("literal value");

            let atom = choice((
                Path::parser().map(Expr::Path),
                literal.map(Expr::Literal),
                block_parser.clone().map(Expr::Block),
                just(Token::Loop).ignore_then(block_parser.clone()).map(Expr::Loop),
                just(Token::While)
                    .ignore_then(expr_parser.then(block_parser.clone()))
                    .map(|(expr, block)| Expr::While(Box::new(expr), block)),
                parens_parser,
                array
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
                        select! {
                            $(Token::$token => BinOp::$bin_op),+
                        },
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
                    |func, args, _| {
                        Expr::Call(Box::new(func), args)
                    }
                ),

                // then go the unary ops
                prefix(
                    UnOp::BINDING_POWER,
                    select! {
                        Token::Star => UnOp::Deref,
                        Token::Not => UnOp::Not,
                        Token::Minus => UnOp::Neg,
                    },
                    |un_op, expr, _| Expr::UnOp(un_op, Box::new(expr))
                ),

                // then the binary operators
                make_bin_op_grouping!(
                    Mul = Star
                    | Div = Slash
                    | Rem = Percent
                    | EMod = EMod
                    | EDiv = EDiv
                ),
                make_bin_op_grouping!(
                    Add = Plus
                    | Sub = Minus
                ),
                make_bin_op_grouping!(
                    Shr = Shr
                    | Shl = Shl
                ),

                make_bin_op_grouping!(BitAnd = And),
                make_bin_op_grouping!(BitOr = Or),
                make_bin_op_grouping!(BitXor = Caret),


                make_bin_op_grouping!(
                    Eq = Equality
                    | Lt = Lt
                    | Le = Le
                    | Ne = Ne
                    | Ge = Ge
                    | Gt = Gt
                ),

                make_bin_op_grouping!(LogicalAnd = LogicalAnd),
                make_bin_op_grouping!(LogicalAnd = LogicalOr),

                // last but not least we have assignments
                infix(
                    right(const { BinOp::MIN_BINDING_POWER - 1 }),
                    select! {
                        Token::Assign => AssignOp::Simple,
                        Token::AddAssign => AssignOp::Add,
                    },
                    |a, assign, c, _| {
                        Expr::Assignment(assign, Box::new((a, c)))
                    }
                )
            ));


            expr
        })
    }
}

impl SealedParseAst for Expr {
    fn parser<'a, I: ValueInput<'a, Token=Token, Span=SimpleSpan>>() -> impl Parser<'a, I, Self, ParserExtra<'a>> + Clone {
        make_recursive_parsers().0
    }
}