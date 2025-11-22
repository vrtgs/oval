use crate::ast::recursive::Recursive;
use crate::interner::Symbol;
use crate::spanned::{Span, Spanned, spanned_struct};
use crate::tokens::{Ident, TokenTy};
use alloc::vec::Vec;
use core::hash::Hash;

pub mod recursive;

#[derive(Debug, Clone)]
pub enum Type {
    Never(TokenTy!["!"]),
    Ident(Ident),
    Array(Recursive<TokenTy!['[', (Type, TokenTy![";"], Expr), ']']>),
    List(Recursive<TokenTy!['[', Type, ']']>),
    Parens(Recursive<TokenTy!['(', Type, ')']>),
    Tuple(Recursive<TokenTy!['(', Vec<Type>, ')']>),
    Fn(
        Recursive<(
            TokenTy!["fn"],
            TokenTy!['(', Vec<Type>, ')'],
            Option<(TokenTy!["->"], Type)>,
        )>,
    ),
}

impl Spanned for Type {
    fn span(&self) -> Span {
        match self {
            Type::Never(never) => never.span(),
            Type::Ident(ident) => ident.span,
            Type::Fn(func) => func.with_inner(|(kw_fn, paren, ret)| {
                let end = ret
                    .as_ref()
                    .map_or_else(|| paren.span(), |(_arrow, ty)| ty.span());

                Span::merge(kw_fn.span(), end)
            }),
            // none of these are recursive, were just querying the delimiters span
            Type::Array(array) => array.span(),
            Type::List(list) => list.span(),
            Type::Parens(parens) => parens.span(),
            Type::Tuple(tuple) => tuple.span(),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum IntegerType {
    Usize,
    U64,
    U32,
    U16,
    U8,

    Isize,
    I64,
    I32,
    I16,
    I8,
}

#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum IntegerRadix {
    Binary = 2,
    Octal = 8,
    Decimal = 10,
    Hex = 16,
}

#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum LiteralValue {
    Integer {
        value: u128,
        radix: IntegerRadix,
        suffix: Option<IntegerType>,
    },
    Str(Symbol),
    Char(char),
    Bool(bool),
}

#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub struct LiteralExpr {
    pub span: Span,
    pub value: LiteralValue,
}

spanned_struct!(LiteralExpr);

#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum BinOpKind {
    // arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Rem,

    // comparisons
    Lt,
    Le,
    Gt,
    Ge,
    // equality
    Eq,
    Ne,
}

#[derive(Debug, Copy, Clone)]
pub struct BinOp {
    pub span: Span,
    pub kind: BinOpKind,
}

spanned_struct!(BinOp);

#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum UnOpKind {
    Not,
    Neg,
}

#[derive(Debug, Copy, Clone)]
pub struct UnOp {
    pub span: Span,
    pub kind: UnOpKind,
}

spanned_struct!(UnOp);

#[derive(Debug, Clone)]
pub struct CallExpr {
    pub callee: Expr,
    pub args: TokenTy!['(', Vec<Expr>, ')'],
}

#[derive(Debug, Clone)]
pub struct IndexExpr {
    pub array: Expr,
    pub index: TokenTy!['[', Expr, ']'],
}

#[derive(Debug, Clone)]
pub struct BinOpExpr {
    pub lhs: Expr,
    pub op: BinOp,
    pub rhs: Expr,
}

#[derive(Debug, Clone)]
pub struct UnOpExpr {
    pub op: UnOp,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct CastAsExpr {
    pub expr: Expr,
    pub kw_as: TokenTy!["as"],
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct LoopExpr {
    pub kw_loop: TokenTy!["loop"],
    pub body: Block,
}

#[derive(Debug, Clone)]
pub struct IfBranch {
    pub kw_if: TokenTy!["if"],
    pub condition: Expr,
    pub body: Block,
}

#[derive(Debug, Clone)]
pub struct IfExpr {
    pub first: IfBranch,
    pub else_if: Vec<(TokenTy!["else"], IfBranch)>,
    pub else_branch: Option<(TokenTy!["else"], Block)>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Error(Span),
    Literal(LiteralExpr),
    Ident(Ident),
    BinaryOp(Recursive<BinOpExpr>),
    UnaryOp(Recursive<UnOpExpr>),
    CastAs(Recursive<CastAsExpr>),
    Call(Recursive<CallExpr>),
    Index(Recursive<IndexExpr>),
    Parens(Recursive<TokenTy!['(', Expr, ')']>),
    Tuple(Recursive<TokenTy!['(', Vec<Expr>, ')']>),
    Array(Recursive<TokenTy!['[', Vec<Expr>, ']']>),
    Return(TokenTy!["return"], Option<Recursive<Expr>>),
    Break(TokenTy!["break"], Option<Recursive<Expr>>),
    Continue(TokenTy!["continue"]),
    Block(Recursive<Block>),
    Loop(Recursive<LoopExpr>),
    If(Recursive<IfExpr>),
}

impl Spanned for Expr {
    fn span(&self) -> Span {
        match self {
            Expr::Error(span) => *span,
            Expr::Literal(lit) => lit.span,
            Expr::Ident(ident) => ident.span,

            // recursive span finder
            Expr::BinaryOp(binop) => binop
                .with_inner(|BinOpExpr { lhs, op: _, rhs }| Span::merge(lhs.span(), rhs.span())),
            Expr::UnaryOp(unop) => {
                unop.with_inner(|UnOpExpr { op, expr }| Span::merge(op.span(), expr.span()))
            }
            Expr::CastAs(cast) => cast.with_inner(|CastAsExpr { expr, kw_as: _, ty }| {
                Span::merge(expr.span(), ty.span())
            }),
            Expr::Call(call_expr) => call_expr
                .with_inner(|CallExpr { callee, args }| Span::merge(callee.span(), args.span())),
            Expr::Index(index_expr) => index_expr
                .with_inner(|IndexExpr { array, index }| Span::merge(array.span(), index.span())),

            Expr::Return(_, expr) | Expr::Break(_, expr) => {
                let mut span = match self {
                    Expr::Return(ret, _) => ret.span(),
                    Expr::Break(kw_break, _) => kw_break.span(),
                    _ => unreachable!(),
                };

                if let Some(expr) = expr.as_ref() {
                    expr.with_inner(|expr| span = Span::merge(span, expr.span()))
                }

                span
            }

            // all these query for the delimiter's span, not the inner expr; and are not recursive
            Expr::Loop(loop_expr) => {
                let expr = loop_expr.get_ref();
                Span::merge(expr.kw_loop.span(), expr.body.span())
            }
            Expr::If(if_ref) => {
                let expr = if_ref.get_ref();
                let last_body = expr
                    .else_branch
                    .as_ref()
                    .map(|(_, block)| block)
                    .or(expr.else_if.last().map(|(_, if_expr)| &if_expr.body))
                    .unwrap_or(&expr.first.body);

                Span::merge(expr.first.kw_if.span(), last_body.span())
            }
            Expr::Block(block) => block.span(),
            Expr::Parens(parens) => parens.get_ref().span(),
            Expr::Tuple(tuple) => tuple.get_ref().span(),
            Expr::Array(array) => array.get_ref().span(),

            // this just queries its token
            Expr::Continue(kw_continue) => kw_continue.span(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct LetStmt {
    pub kw_let: TokenTy!["let"],
    pub kw_mut: Option<TokenTy!["mut"]>,
    pub name: Ident,
    pub ty: Option<(TokenTy![":"], Type)>,
    pub assignment: Option<(TokenTy!["="], Expr)>,
    pub semicolon: TokenTy![";"],
}

impl Spanned for LetStmt {
    fn span(&self) -> Span {
        Span::merge(self.kw_let.span(), self.semicolon.span())
    }
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Item(Recursive<Item>),
    Expression {
        expr: Expr,
        trailing: Option<TokenTy![";"]>,
    },
    Let(LetStmt),
}

#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: TokenTy!['{', Vec<Stmt>, '}'],
}

spanned_struct!(stmts in Block);

#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub kw_pub: Option<TokenTy!["pub"]>,
    pub kw_extern: Option<TokenTy!["extern"]>,
    pub kw_fn: TokenTy!["fn"],
    pub name: Ident,
    pub args: TokenTy!['(', Vec<(Ident, TokenTy![":"], Type)>, ')'],
    pub ret: Option<(TokenTy!["->"], Type)>,
}

impl Spanned for FunctionSignature {
    fn span(&self) -> Span {
        let start = self
            .kw_pub
            .as_ref()
            .map(Spanned::span)
            .or(self.kw_extern.as_ref().map(Spanned::span))
            .unwrap_or(self.kw_fn.span());

        let end = self
            .ret
            .as_ref()
            .map_or(self.args.span(), |(_, ty)| ty.span());

        Span::merge(start, end)
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    pub signature: FunctionSignature,
    pub body: Block,
}

impl Spanned for Function {
    fn span(&self) -> Span {
        Span::merge(self.signature.span(), self.body.span())
    }
}

#[derive(Debug, Clone)]
pub struct ConstItem {
    pub kw_pub: Option<TokenTy!["pub"]>,
    pub kw_extern: Option<TokenTy!["extern"]>,
    pub kw_const: TokenTy!["const"],
    pub name: Ident,
    pub ty_colon: TokenTy![":"],
    pub ty: Type,
    pub eq_token: TokenTy!["="],
    pub assignment: Expr,
    pub semicolon: TokenTy![";"],
}

impl Spanned for ConstItem {
    fn span(&self) -> Span {
        let start = self
            .kw_pub
            .as_ref()
            .map(Spanned::span)
            .or(self.kw_extern.as_ref().map(Spanned::span))
            .unwrap_or(self.kw_const.span());

        Span::merge(start, self.semicolon.span())
    }
}

#[derive(Debug, Clone)]
pub enum Item {
    Function(Function),
    Const(ConstItem),
}

impl Spanned for Item {
    fn span(&self) -> Span {
        match self {
            Item::Function(func) => func.span(),
            Item::Const(const_item) => const_item.span(),
        }
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum Attributes {}

#[derive(Debug)]
pub struct OvalModule {
    pub attributes: Vec<Attributes>,
    pub items: Vec<Item>,
}
