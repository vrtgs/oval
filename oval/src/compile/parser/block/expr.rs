use alloc::boxed::Box;
use alloc::vec::Vec;
use crate::compile::error::SyntaxError;
use crate::compile::parser::block::Block;
use crate::compile::parser::{Tuple, ParseAst, Parser, TupleOrParens};
use crate::compile::span::SimpleSpan;
use crate::compile::tokenizer::{LiteralKind, TokenKind, TokenTreeKind};
use crate::symbol::Path;

#[derive(Debug, Copy, Clone)]
pub enum AssignOpKind {
    /// `=`
    Simple,
    /// `+=`
    Add
}

#[derive(Debug, Copy, Clone)]
pub struct AssignOp {
    span: SimpleSpan,
    assign_op_kind: AssignOpKind
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

#[derive(Debug, Copy, Clone)]
pub enum BinOpKind {
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

#[derive(Debug, Copy, Clone)]
pub struct BinOp {
    kind: BinOpKind,
    span: SimpleSpan
}
impl BinOp {
    fn precedence(&self) -> u8 {
        match self.kind {
            BinOpKind::Mul | BinOpKind::Div | BinOpKind::Rem | BinOpKind::EMod | BinOpKind::EDiv => 10,
            BinOpKind::Add | BinOpKind::Sub => 9,
            BinOpKind::Shl | BinOpKind::Shr => 8,
            BinOpKind::BitAnd => 7,
            BinOpKind::BitXor => 6,
            BinOpKind::BitOr => 5,
            BinOpKind::Eq | BinOpKind::Lt | BinOpKind::Le | BinOpKind::Ne | BinOpKind::Ge | BinOpKind::Gt => 4,
            BinOpKind::LogicalAnd => 3,
            BinOpKind::LogicalOr => 2,
        }
    }
}

#[derive(Debug)]
pub enum Expr {
    Path(Path),
    Tuple(Vec<Expr>),
    Parens(Box<Expr>),
    BinOp(BinOp, Box<(Expr, Expr)>),
    Unary(UnOp, Box<Expr>),
    Literal(LiteralKind, SimpleSpan),
    Block(Block),
    Loop(Block),
    /// in the expr `x = b + z` `x` will be the first expr, `b + z` will be the second
    /// and the assign op will be `=`
    Assignment(AssignOp, Box<(Expr, Expr)>),

    // TODO: WhileLoop(Box<Expr>, Block),
    // TODO: ForLoop
    // WISHLIST: Closure
}

impl ParseAst for Expr {
    fn parse_inner<'src>(parser: &mut Parser<'src, '_, '_>) -> crate::compile::error::Result<'src, Self> {
        parse_expr(parser)
    }
}

fn parse_expr<'src>(parser: &mut Parser<'src, '_, '_>) -> crate::compile::error::Result<'src, Expr> {
    // Parse the left-hand side expression (starting with unary operators or primary expressions)
    let lhs = parse_unary(parser)?;

    // Now handle assignments, which are right-associative and have the lowest precedence
    if let Some(assign_op) = parse_assign_op(parser) {
        // After assignment operator, parse the right-hand side expression
        let rhs = parse_expr(parser)?;
        return Ok(Expr::Assignment(assign_op, Box::new((lhs, rhs))));
    }

    // If no assignment, parse binary expressions with min precedence 1
    parse_binary(parser, 1)
}

fn parse_assign_op<'src>(parser: &mut Parser<'src, '_, '_>) -> Option<AssignOp> {
    let token = parser.peek()?;
    let span = token.span();
    let kind = match token.kind() {
        TokenTreeKind::Assign => AssignOpKind::Simple,
        TokenTreeKind::AddAssign => AssignOpKind::Add,
        _ => return None,
    };
    parser.next();
    Some(AssignOp { span, assign_op_kind: kind })
}


fn parse_binary<'src>(parser: &mut Parser<'src, '_, '_>, min_prec: u8) -> crate::compile::error::Result<'src, Expr> {
    let mut lhs = parse_unary(parser)?;

    while let Some(bin_op) = parse_bin_op(parser) {
        let prec = bin_op.precedence();
        if prec < min_prec {
            break;
        }
        let rhs = parse_binary(parser, prec + 1)?;
        lhs = Expr::BinOp(bin_op, Box::new((lhs, rhs)));
    }

    Ok(lhs)
}


fn parse_bin_op<'src>(parser: &mut Parser<'src, '_, '_>) -> Option<BinOp> {
    let token = parser.peek()?;
    let span = token.span();
    let kind = match token.kind() {
        TokenTreeKind::Plus => BinOpKind::Add,
        TokenTreeKind::Minus => BinOpKind::Sub,
        TokenTreeKind::Star => BinOpKind::Mul,
        TokenTreeKind::Slash => BinOpKind::Div,
        TokenTreeKind::Percent => BinOpKind::Rem,
        TokenTreeKind::EDiv => BinOpKind::EDiv,
        TokenTreeKind::EMod => BinOpKind::EMod,
        TokenTreeKind::LogicalAnd => BinOpKind::LogicalAnd,
        TokenTreeKind::LogicalOr => BinOpKind::LogicalOr,
        TokenTreeKind::Caret => BinOpKind::BitXor,
        TokenTreeKind::And => BinOpKind::BitAnd,
        TokenTreeKind::Or => BinOpKind::BitOr,
        TokenTreeKind::Shl => BinOpKind::Shl,
        TokenTreeKind::Shr => BinOpKind::Shr,
        TokenTreeKind::Equality => BinOpKind::Eq,
        TokenTreeKind::Lt => BinOpKind::Lt,
        TokenTreeKind::Le => BinOpKind::Le,
        TokenTreeKind::Ne => BinOpKind::Ne,
        TokenTreeKind::Ge => BinOpKind::Ge,
        TokenTreeKind::Gt => BinOpKind::Gt,
        _ => return None,
    };
    parser.next();
    Some(BinOp { kind, span })
}

fn parse_unary<'src>(parser: &mut Parser<'src, '_, '_>) -> crate::compile::error::Result<'src, Expr> {
    let token = parser.peek();
    let op = match token.map(|t| t.kind()) {
        Some(TokenTreeKind::Star) => Some(UnOp::Deref),
        Some(TokenTreeKind::Not) => Some(UnOp::Not),
        Some(TokenTreeKind::Minus) => Some(UnOp::Neg),
        _ => None,
    };

    if let Some(op) = op {
        parser.next();
        let expr = parse_unary(parser)?;
        return Ok(Expr::Unary(op, Box::new(expr)));
    }

    parse_primary(parser)
}

fn parse_primary<'src>(parser: &mut Parser<'src, '_, '_>) -> crate::compile::error::Result<'src, Expr> {
    let token = parser.peek();
    match token.map(|t| t.kind()) {
        Some(TokenTreeKind::Ident | TokenTreeKind::DoubleColon) => {
            let path = parser.parse::<Path>()?;
            Ok(Expr::Path(path))
        }
        Some(&TokenTreeKind::Literal(lit)) => {
            let token = parser.next().unwrap();
            Ok(Expr::Literal(lit, token.span()))
        }
        Some(TokenTreeKind::Paren(paren)) => {
            let mut sub_parser = parser.sub_parser(paren);
            let expressions = sub_parser.parse_list::<Expr, Tuple>(TokenKind::Comma)?;
            Ok(match expressions {
                TupleOrParens::Parens(x) => Expr::Parens(Box::new(x)),
                TupleOrParens::Tuple(tuple) => Expr::Tuple(tuple)
            })
        }
        Some(TokenTreeKind::Bracket(_)) => {
            let block = parser.parse::<Block>()?;
            Ok(Expr::Block(block))
        }
        Some(TokenTreeKind::Loop) => {
            parser.next();
            let block = parser.parse::<Block>()?;
            Ok(Expr::Loop(block))
        }
        _ => Err(parser.syntax_error(SyntaxError::custom(token.map(|t| t.span()), "expected expression")))
    }
}

