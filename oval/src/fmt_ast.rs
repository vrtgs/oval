use std::fmt::{Debug, Display, Formatter, Write};
use oval::ast::{BinOpExpr, BinOpKind, Block, CallExpr, CastAsExpr, ConstItem, Expr, Function, FunctionSignature, IfBranch, IndexExpr, IntegerBase, IntegerSuffix, Item, LetStmt, LiteralExpr, LiteralValue, OvalModule, Stmt, Type, UnOpExpr, UnOpKind};
use oval::interner::Interner;
use oval::tokens::Ident;
use oval::TokenTy;

#[derive(Copy, Clone)]
struct RecurseData<'a> {
    interner: &'a Interner,
    depth: u32
}

impl<'a> RecurseData<'a> {
    pub fn one_deeper(self) -> Self {
        Self {
            interner: self.interner,
            depth: self.depth.checked_add(1)
                .expect("that's way too deep")
        }
    }
}

trait FmtAst {
    fn ast_write<'a>(&'a self, data: RecurseData<'a>, f: &mut Formatter) -> core::fmt::Result;

    fn display<'a>(&'a self, data: RecurseData<'a>) -> impl Display + 'a {
        AstDisplay {
            ast: self,
            data
        }
    }

    fn display_list_seperated_by<'a>(
        list: &'a [Self],
        data: RecurseData<'a>,
        seperator: &'static str
    ) -> impl Display + 'a
    where Self: Sized {
        AstDisplayList {
            list,
            data,
            seperator
        }
    }

    fn display_comma_list<'a>(
        list: &'a [Self],
        data: RecurseData<'a>
    ) -> impl Display + 'a
        where Self: Sized
    {
        Self::display_list_seperated_by(
            list,
            data,
            ", "
        )
    }
}

struct AstDisplay<'a, T: ?Sized> {
    ast: &'a T,
    data: RecurseData<'a>
}

impl<T: ?Sized + FmtAst> Display for AstDisplay<'_, T> {
    #[inline(always)]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        T::ast_write(
            self.ast,
            self.data,
            f
        )
    }
}

struct AstDisplayList<'a, T> {
    list: &'a [T],
    data: RecurseData<'a>,
    seperator: &'static str
}

impl<'a, T: FmtAst> Display for AstDisplayList<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let [head @ .., tail] = self.list else {
            return Ok(())
        };

        for ast in head {
            T::ast_write(ast, self.data, f)?;
            f.write_str(self.seperator)?;
        }

        T::ast_write(tail, self.data, f)
    }
}

impl FmtAst for Type {
    fn ast_write<'a>(&'a self, data: RecurseData<'a>, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Type::Never(_) => f.write_char('!'),
            Type::Ident(ident) => f.write_str(data.interner.resolve(ident.symbol())),
            Type::Array(array) => array.with_inner(|list| {
                let (ty, _semicolon, expr) = &list.0;

                write!(f, "[{ty}; {expr}]", ty = ty.display(data), expr = expr.display(data))
            }),
            Type::List(list) => list.with_inner(|list| {
                write!(f, "[{}]", list.0.display(data))
            }),
            Type::Parens(paren) => paren.with_inner(|paren| {
                write!(f, "({})", paren.0.display(data))
            }),
            Type::Fn(func) => func.with_inner(|func| {
                let (_kw_fn, args, ret) = func;
                let args = args.0.as_slice();
                write!(
                    f,
                    "fn({})",
                    Type::display_comma_list(args, data)
                )?;

                if let Some((_arrow, ret)) = ret {
                    write!(f, " -> {}", ret.display(data))?
                }

                Ok(())
            }),
            Type::Tuple(tuple) => {
                tuple.with_inner(|tuple| {
                    match tuple.0.as_slice() {
                        // unit
                        [] => f.write_str("()"),
                        [one] => write!(f, "({},)", one.display(data)),
                        list => {
                            write!(f, "({})", Type::display_comma_list(list, data))
                        }
                    }
                })
            }
        }
    }
}

impl FmtAst for LiteralExpr {
    fn ast_write<'a>(&'a self, data: RecurseData<'a>, f: &mut Formatter) -> std::fmt::Result {
        match self.value {
            LiteralValue::Bool(val) => f.write_str(if val { "true" } else { "false" }),
            LiteralValue::Integer {
                base,
                number,
                suffix
            } => {
                'write_base_prefix: {
                    let prefix = match base {
                        IntegerBase::Decimal => break 'write_base_prefix,
                        IntegerBase::Binary => "0b",
                        IntegerBase::Octal => "0o",
                        IntegerBase::Hex => "0x",
                    };
                    f.write_str(prefix)?
                }

                f.write_str(data.interner.resolve(number))?;

                if let Some(suffix) = suffix {
                    let suffix = match suffix {
                        IntegerSuffix::Usize => "_usize",
                        IntegerSuffix::U64 => "_u64",
                        IntegerSuffix::U32 => "_u32",
                        IntegerSuffix::U16 => "_u16",
                        IntegerSuffix::U8 => "_u8",
                        IntegerSuffix::Isize => "_isize",
                        IntegerSuffix::I64 => "_i64",
                        IntegerSuffix::I32 => "_i32",
                        IntegerSuffix::I16 => "_i16",
                        IntegerSuffix::I8 => "_i8",
                    };

                    f.write_str(suffix)?
                }
                Ok(())
            },
            LiteralValue::Str(symbol) => {
                let str_literal = data.interner.resolve(symbol);
                <str as Debug>::fmt(str_literal, f)
            },
        }
    }
}

impl FmtAst for Expr {
    fn ast_write<'a>(&'a self, data: RecurseData<'a>, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Expr::Error(_) => f.write_str("<error>"),
            Expr::Literal(lit) => lit.ast_write(data, f),
            Expr::Ident(ident) => f.write_str(data.interner.resolve(ident.symbol())),
            Expr::BinaryOp(op) => {
                op.with_inner(move |BinOpExpr { lhs, op, rhs }| {
                    let op = match op.kind {
                        BinOpKind::Add => "+",
                        BinOpKind::Sub => "-",
                        BinOpKind::Mul => "*",
                        BinOpKind::Div => "/",
                        BinOpKind::Rem => "%",

                        BinOpKind::Lt => "<",
                        BinOpKind::Le => "<=",
                        BinOpKind::Gt => ">",
                        BinOpKind::Ge => ">=",

                        BinOpKind::Eq => "==",
                        BinOpKind::Ne => "!=",
                    };

                    write!(
                        f,
                        "{lhs} {op} {rhs}",
                        lhs = lhs.display(data),
                        rhs = rhs.display(data)
                    )
                })
            }
            Expr::UnaryOp(op) => {
                op.with_inner(move |UnOpExpr { op, expr }| {
                    let op = match op.kind {
                        UnOpKind::Not => '!',
                        UnOpKind::Neg => '-'
                    };

                    f.write_char(op)?;
                    expr.ast_write(data, f)
                })
            }
            Expr::CastAs(cast) => {
                cast.with_inner(|CastAsExpr { expr, kw_as: _, ty }| {
                    write!(f, "{expr} as {ty}", expr = expr.display(data), ty = ty.display(data))
                })
            }
            Expr::Call(call_expr) => {
                call_expr.with_inner(|CallExpr { callee, args }| {
                    write!(
                        f,
                        "{callee}({args})",
                        callee = callee.display(data),
                        args = Expr::display_comma_list(&args.0, data)
                    )
                })
            }
            Expr::Index(index_expr) => {
                index_expr.with_inner(|IndexExpr { array, index }| {
                    write!(
                        f,
                        "{array}[{index}]",
                        array = array.display(data),
                        index = index.0.display(data)
                    )
                })
            }
            Expr::Parens(parens) => {
                parens.with_inner(|inner| {
                    write!(f, "({})", inner.0.display(data))
                })
            }
            Expr::Tuple(tuple) => {
                tuple.with_inner(|tuple| {
                    match tuple.0.as_slice() {
                        [] => f.write_str("()"),
                        [one] => write!(f, "({},)", one.display(data)),
                        expressions => {
                            write!(f, "({})", Expr::display_comma_list(expressions, data))
                        }
                    }
                })
            },
            Expr::List(list) => {
                list.with_inner(|tuple| {
                    let expressions = tuple.0.as_slice();

                    write!(f, "[{}]", Expr::display_comma_list(expressions, data))
                })
            },
            Expr::Return(_, expr)
            | Expr::Break(_, expr) => {
                let name = match self {
                    Expr::Return(_, _) => "return",
                    Expr::Break(_, _) => "break",
                    _ => unreachable!()
                };

                match expr {
                    None => f.write_str(name),
                    Some(expr) => expr.with_inner(|inner| {
                        write!(f, "{name} {}", inner.display(data))
                    }),
                }
            },
            Expr::Continue(_) => f.write_str("continue"),


            Expr::Block(block) => block.with_inner(|block| {
                block.ast_write(data, f)
            }),
            Expr::Loop(loop_expr) => loop_expr.with_inner(|expr| {
                write!(f, "loop {}", expr.body.display(data))
            }),
            Expr::If(if_expr) => if_expr.with_inner(|if_expr| {
                let write_branch = move |branch: &IfBranch, f: &mut Formatter| {
                    f.write_str("if ")?;
                    branch.condition.ast_write(data, f)?;
                    f.write_char(' ')?;
                    branch.body.ast_write(data, f)
                };

                write_branch(&if_expr.first, f)?;
                for (_else, branch) in &if_expr.else_if {
                    f.write_str(" else ")?;
                    write_branch(branch, f)?
                }

                if let Some((_else, body)) = if_expr.else_branch.as_ref() {
                    f.write_str(" else ")?;
                    body.ast_write(data, f)?
                }

                Ok(())
            }),
        }
    }
}

impl FmtAst for Block {
    fn ast_write<'a>(&'a self, data: RecurseData<'a>, f: &mut Formatter) -> std::fmt::Result {
        let stmts = self.stmts.0.as_slice();

        if stmts.is_empty() {
            return f.write_str("{}");
        }

        let prev_data = data;
        let data = prev_data.one_deeper();

        static PADDING_CHEAP_DATA: [[u8; 4]; 64] = [[b' '; 4]; 64];

        const PADDING_CHEAP: &str = match str::from_utf8(PADDING_CHEAP_DATA.as_flattened()) {
            Ok(padding) => padding,
            Err(_) => panic!("padding wasn't ascii space")
        };

        let write_padding = |depth: u32, f: &mut Formatter| {
            let mut padding = u64::from(depth) * 4;
            let Ok(padding_len) = u64::try_from(PADDING_CHEAP.len()) else {
                // padding_count < padding_cheap; this is impossible but
                // this is the correct way to handle that case
                return f.write_str(&PADDING_CHEAP[..padding as usize]);
            };

            while let Some(new_padding) = padding.checked_sub(padding_len) {
                f.write_str(PADDING_CHEAP)?;
                padding = new_padding;
            }

            // now padding < padding_len <= usize
            // so the cast bellow is safe
            let padding_final = padding as usize;
            f.write_str(&PADDING_CHEAP[..padding_final])?;
            Ok(())
        };

        f.write_str("{\n")?;
        for stmt in stmts {
            write_padding(data.depth, f)?;

            match stmt {
                Stmt::Item(item) => item.with_inner(|item| {
                    item.ast_write(data, f)
                })?,
                Stmt::Let(LetStmt {
                              kw_let: _,
                              kw_mut,
                              name,
                              ty,
                              assignment,
                              semicolon: _
                          }) => {

                    f.write_str("let ")?;
                    if kw_mut.is_some() {
                        f.write_str("mut ")?
                    }
                    f.write_str(data.interner.resolve(name.symbol()))?;

                    if let Some((_colon, ty)) = ty {
                        write!(f, ": {}", ty.display(data))?
                    }

                    if let Some((_eq, expr)) = assignment {
                        write!(f, " = {}", expr.display(data))?
                    }

                    f.write_char(';')?
                }
                Stmt::Expression { expr, trailing } => {
                    expr.ast_write(data, f)?;
                    if trailing.is_some() {
                        f.write_char(';')?;
                    }
                }
            }

            f.write_char('\n')?
        }
        write_padding(prev_data.depth, f)?;
        f.write_str("}")
    }
}

impl FmtAst for FunctionSignature {
    fn ast_write<'a>(&'a self, data: RecurseData<'a>, f: &mut Formatter) -> std::fmt::Result {
        if self.kw_pub.is_some() {
            f.write_str("pub ")?
        }

        if self.kw_extern.is_some() {
            f.write_str("extern ")?
        }

        let name = self.name.symbol();
        let name = data.interner.resolve(name);

        #[allow(non_local_definitions)]
        impl FmtAst for (Ident, TokenTy![":"], Type) {
            fn ast_write<'a>(&'a self, data: RecurseData<'a>, f: &mut Formatter) -> std::fmt::Result {
                let (arg_name, _, ty) = self;

                write!(
                    f,
                    "{name}: {ty}",
                    name = data.interner.resolve(arg_name.symbol()),
                    ty = ty.display(data),
                )
            }
        }

        let args = <(Ident, TokenTy![":"], Type) as FmtAst>::display_comma_list(
            &self.args.0,
            data
        );

        write!(f, "fn {name}({args}) ")?;
        if let Some((_arrow, ret_ty)) = self.ret.as_ref() {
            write!(f, "-> {} ", ret_ty.display(data))?
        }

        Ok(())
    }
}

impl FmtAst for Function {
    fn ast_write<'a>(&'a self, data: RecurseData<'a>, f: &mut Formatter) -> std::fmt::Result {
        self.signature.ast_write(data, f)?;
        self.body.ast_write(data, f)
    }
}

impl FmtAst for ConstItem {
    fn ast_write<'a>(&'a self, data: RecurseData<'a>, f: &mut Formatter) -> std::fmt::Result {
        if self.kw_pub.is_some() {
            f.write_str("pub ")?
        }

        if self.kw_extern.is_some() {
            f.write_str("extern ")?
        }

        let name = self.name.symbol();
        let name = data.interner.resolve(name);

        write!(
            f,
            "const {name}: {ty} = {expr};",
            ty = self.ty.display(data),
            expr = self.assignment.display(data)
        )
    }
}

impl FmtAst for Item {
    fn ast_write<'a>(&'a self, data: RecurseData<'a>, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Item::Function(func) => func.ast_write(data, f),
            Item::Const(const_item) => const_item.ast_write(data, f)
        }
    }
}

impl FmtAst for OvalModule {
    fn ast_write<'a>(&'a self, data: RecurseData<'a>, f: &mut Formatter) -> std::fmt::Result {
        let fmt = Item::display_list_seperated_by(
            &self.items,
            data,
            "\n\n"
        );

        Display::fmt(&fmt, f)
    }
}

pub fn display_module<'a>(module: &'a OvalModule, interner: &'a Interner) -> impl Display + 'a {
    module.display(RecurseData {
        interner,
        depth: 0
    })
}