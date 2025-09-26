use alloc::borrow::Cow;
use alloc::vec;
use crate::ast::{BinOp, Block, CallExpr, Expr, Function, Item, LetStmt, LiteralExpr, LiteralValue, OvalModule, Stmt, Type, UnOp, UnOpKind, BinOpKind, ConstItem, UnOpExpr, BinOpExpr, CastAsExpr, IndexExpr, LoopExpr, IntegerSuffix, IntegerBase, IfExpr, IfBranch, FunctionSignature};
use crate::parser::parser_impl::ext::{OvalParserExt, recursive_parser, recover_nested_delimiters, static_parser, recover_nested_delimiters_extra, static_unsized_parser};
use crate::parser::{AstParse, InputTape, OvalParser, ParserData, ParserState};
use crate::tokens::{Arrow, Equals, Colon, Comma, Extern, TokenKind, Fn, Ident, Let, Literal, Mut, Pub, Semicolon, Const, As, Not, Loop, Return, Break, If, Else, CurlyBrace, Token, SquareBracket};
use alloc::vec::Vec;
use chumsky::{IterParser, Parser};
use chumsky::extra::SimpleState;
use chumsky::prelude::via_parser;
use crate::ast::recursive::Recursive;
use chumsky::primitive::group as parse_group;
use crate::interner::Interner;
use crate::parser::parser_impl::{ParserError, Pattern};
use crate::spanned::Span;
use crate::tokens::TokenTy;
use crate::spanned::Spanned;

macro_rules! impl_suffixes {
    (
        suffix = $suffix_expr: expr;
        number = $number: expr;
        errors = $errors: expr;
        span = $span: expr;
        suffix_name = $suffix_name: ident;
        $($suffix: literal $name: ident),+ $(,)?
    ) => {
        match $suffix_expr {
            "" => None,
            $($suffix => Some($suffix_name::$name),)+
            suffix => {
                $errors.push(ParserError::custom(
                    $span,
                    "unknown integer suffix",
                    format_args!("unknown integer suffix `{suffix}`")
                ));
                None
            }
        }
    };
}

impl AstParse for LiteralExpr {
    fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>() -> impl OvalParser<'src, I, Self, E> {
        pub fn parse_integer_literal<'src, I: InputTape<'src>, E: ParserError<'src, I>>(
            span: Span,
            number_full: &str,
            interner: &mut Interner,
            errors: &mut Vec<E>
        ) -> LiteralValue {
            let mut hit_number_after_hitting_underscore = false;
            let mut underscore_count = 0;
            let index = number_full
                .find(|char: char| match char {
                    '0'..='9' => {
                        if underscore_count != 0 {
                            hit_number_after_hitting_underscore = true;
                        }
                        false
                    },
                    '_' => {
                        underscore_count += 1;
                        false
                    }
                    _ => true
                })
                .unwrap_or(number_full.len());

            // include the suffix starter with the suffix
            let (number, suffix) = number_full.split_at(index);

            let number_is_clean = !hit_number_after_hitting_underscore;

            let number = match number_is_clean {
                true => Cow::Borrowed(&number[..number.len()-underscore_count]),
                false => Cow::Owned(number.replace("_", ""))
            };

            let suffix = impl_suffixes! {
                suffix = suffix;
                number = number;
                errors = errors;
                span = span;
                suffix_name = IntegerSuffix;

                "isize" Isize,
                "i64" I64,
                "i32" I32,
                "i16" I16,
                "i8" I8,

                "usize" Usize,
                "u64" U64,
                "u32" U32,
                "u16" U16,
                "u8" U8,
            };

            let symbol = interner.get_or_intern(&number);
            LiteralValue::Integer {
                base: IntegerBase::Decimal,
                number: symbol,
                suffix
            }
        }

        static_parser! {
            let parser = chumsky::select! {
                TokenKind::Literal(lit) => lit
            };

            let parser = parser.map_with(|literal, extra| {
                // type hints for the compiler
                let span: Span = extra.span();
                let state: &mut SimpleState<ParserState<E::Error>> = extra.state();
                let state: &mut ParserState<E::Error> = state;

                let text = state.text;
                let interner = &mut *state.interner;
                let literal_str = &text[span.into_range()];

                let value = match literal {
                    Literal::Integer => parse_integer_literal(
                        span,
                        literal_str,
                        interner,
                        &mut state.produced_errors
                    ),
                    Literal::Bool(bool) => LiteralValue::Bool(bool),
                    Literal::String
                    | Literal::Char
                    | Literal::Float => todo!()
                };

                LiteralExpr {
                    span,
                    value
                }
            });

            parser.labelled(Pattern::Label("literal"))
        }
    }
}

macro_rules! spanned_op {
    ($op: ident {
        $($token_kind: ident => $op_kind: ident),+ $(,)?
    }) => {{
        paste::paste! {
            chumsky::select! {
                $(TokenKind::$token_kind = e => $op {
                    span: e.span(),
                    kind: [<$op Kind>]::$op_kind
                }),+
            }
        }
    }};
}

fn fold_binop(lhs: Expr, (op, rhs): (BinOp, Expr)) -> Expr {
    Expr::BinaryOp(Recursive::new(BinOpExpr {
        lhs,
        op,
        rhs
    }))
}

macro_rules! chained_binop_parers {
    (
        @chained start = $start: expr;
    ) => { $start };


    (
        @chained start = $start: expr;
        $group_name: ident: no_chaining {
            $($token_kind: ident => $op_kind: ident),+ $(,)?
        }
        $($rest:tt)*
    ) => {{
        let current_op = spanned_op! {
            BinOp {
                $($token_kind => $op_kind),+
            }
        };

        let last_parser = $start;

        let parser = last_parser.try_foldl(
            current_op.then(last_parser).repeated(),
            |lhs, (op, mut rhs), with| {
                // we fold left, so we only need to check the left hand side
                if let Expr::BinaryOp(ref expr) = lhs {
                    if let &BinOpExpr {
                        op: BinOp {
                            span: lhs_op_span,
                            kind: $(BinOpKind::$op_kind)|+,
                        },
                        ..
                    } = expr.get_ref() {
                        let span: Span = with.span();
                        let state: &mut SimpleState<ParserState<_>> = with.state();
                        let state: &mut ParserState<_> = state;
                        state.produced_errors.push(ParserError::custom_with_labels(
                            span,
                            "comparison operators cannot be chained",
                            [
                                (
                                    lhs_op_span,
                                    "chaining happens here"
                                ),
                                (
                                    op.span,
                                    "and here"
                                ),
                            ]
                        ));

                        rhs = Expr::Error(rhs.span());
                    }
                }

                Ok(fold_binop(lhs, (op, rhs)))
            }
        );

        chained_binop_parers!(
            @chained start = parser;
            $($rest)*
        )
    }};

    (
        @chained start = $start: expr;
        $group_name: ident:  {
            $($tt:tt)+
        }
        $($rest:tt)*
    ) => {{
        let current_op = spanned_op! {
            BinOp {
                $($tt)+
            }
        };

        let last_parser = $start;

        let parser = last_parser.foldl(
            current_op.then(last_parser).repeated(),
            fold_binop
        );
        chained_binop_parers!(
            @chained start = parser;
            $($rest)*
        )
    }};

    (
        start = $start: expr;
        $($group_name: ident: $(no_chaining $([@$no_chains:tt])?)? {
            $($tt:tt)+
        })+
    ) => {
        chained_binop_parers! {
            @chained start = $start;
            $($group_name: $(no_chaining $([$no_chains])?)? {
                $($tt)+
            })+
        }
    };
}

macro_rules! make_expr_parser {
    (
        $expr: ident : Parser<Expr>
        $list: ident : Parser<Vec<Expr>>
        atom = $atom: expr
    ) => {static_parser! {
        let $expr = recursive_parser::<Expr, I, E>();

        let $list = $expr
            .separated_by(Comma::parser())
            .allow_trailing()
            .collect();

        let any_paren = recover_nested_delimiters_extra::<TokenTy!['(', (), ')'], _, _, _>(drop)
            .map(|parens| {
                Expr::Tuple(Recursive::new(parens.map(|()| vec![])))
            });

        let any_list = recover_nested_delimiters_extra::<TokenTy!['[', (), ']'], _, _, _>(drop)
            .map(|bracket| {
                Expr::List(Recursive::new(bracket.map(|()| vec![])))
            });

        let primary = $atom
            .recover_with(via_parser(any_paren))
            .recover_with(via_parser(any_list));

        // call have the highest binding power
        // so start with them
        // calls are left associative simply due to them being at the end of an expression
        enum CallType {
            Call(TokenTy!['(', Vec<Expr>, ')']),
            Index(TokenTy!['[', Expr, ']']),
        }

        let call = primary.foldl(
            chumsky::primitive::choice((
                $list.in_parens().map(CallType::Call),
                $expr.in_square_brackets().map(CallType::Index)
            )).repeated(),
            |expr, call_ty| {
                match call_ty {
                    CallType::Call(args) => {
                        Expr::Call(Recursive::new(CallExpr {
                            callee: expr,
                            args
                        }))
                    }
                    CallType::Index(index) => Expr::Index(Recursive::new(IndexExpr {
                        array: expr,
                        index
                    })),
                }
            }
        );


        let unop = spanned_op! {
            UnOp {
                Minus => Neg,
                Not => Not
            }
        };

        // unary comes next in the precedence list
        let unary = unop.repeated().foldr(call, |op, expr| {
            Expr::UnaryOp(Recursive::new(UnOpExpr {
                op,
                expr,
            }))
        });

        let as_cast = unary.foldl(
            As::parser().then(Type::parser()).repeated(),
            |expr, (kw_as, ty)| Expr::CastAs(Recursive::new(CastAsExpr {
                expr,
                kw_as,
                ty,
            }))
        );

        let binop_applied = chained_binop_parers! {
            start = as_cast;
            product: {
                Star => Mul,
                Slash => Div,
                Percent => Rem
            }
            sum: {
                Plus => Add,
                Minus => Sub
            }

            comp: no_chaining {
                LessThan => Lt,
                LessthanOrEqual => Le,
                GreaterThan => Gt,
                GreaterThanOrEqual => Ge,

                IsEquality => Eq,
                IsNotEqual => Ne,
            }
        };


        binop_applied.labelled(Pattern::Label("expression"))
    }};
}

macro_rules! declare_expression {
    (
        $expr: ident: Parser<Expr>
        $list: ident: Parser<Vec<Expr>>
        AtomWithBlock {
            $($parser_with_block: expr),+ $(,)?
        }
        AtomWithoutBlock {
            $($parser_no_block: expr),+ $(,)?
        }
    ) => {
        pub(crate) const fn expr_with_block_parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>() -> impl OvalParser<'src, I, Expr, E> {
            static_parser! {
                let $expr = Expr::parser();
                chumsky::primitive::choice((
                    $($parser_with_block,)+
                ))
            }
        }

        pub(crate) const fn expr_without_block_parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>() -> impl OvalParser<'src, I, Expr, E> {
            make_expr_parser! {
                $expr: Parser<Expr>
                $list: Parser<Vec<Expr>>
                atom = chumsky::primitive::choice((
                    $($parser_no_block,)+
                ))
            }
        }

        impl AstParse for Expr {
            fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>() -> impl OvalParser<'src, I, Self, E> {
                make_expr_parser! {
                    $expr: Parser<Expr>
                    $list: Parser<Vec<Expr>>
                    atom = chumsky::primitive::choice((
                        $($parser_with_block,)+
                        $($parser_no_block,)+
                    ))
                }
            }
        }
    };
}


declare_expression! {
    expr: Parser<Expr>
    list: Parser<Vec<Expr>>
    AtomWithBlock {
        Loop::parser().then(Block::parser()).map(|(kw_loop, body)| {
            Expr::Loop(Recursive::new(LoopExpr {
                kw_loop,
                body
            }))
        }),
        Block::parser().map(|block| Expr::Block(Recursive::new(block))),
        {
            let if_branch = chumsky::primitive::group((
                If::parser(),
                expr,
                Block::parser()
            ));

            let if_branch = if_branch.map(|(kw_if, condition, body)| IfBranch {
                kw_if,
                condition,
                body
            });

            let if_expr = chumsky::primitive::group((
                if_branch,
                Else::parser().then(if_branch).repeated().collect(),
                Else::parser().then(Block::parser()).or_not(),
            ));

            if_expr.map(|(first, else_if, else_branch)| {
                let expr = IfExpr {
                    first,
                    else_if,
                    else_branch
                };
                Expr::If(Recursive::new(expr))
            })
        }
    }

    AtomWithoutBlock {
        expr.recursive_tuple(
            Expr::Parens,
            Expr::Tuple,
        ),
        LiteralExpr::parser().map(Expr::Literal),
        list
            .in_square_brackets()
            .map(|list| {
                Expr::List(Recursive::new(list))
            }),
        Ident::parser().map(Expr::Ident),
        Return::parser().then(expr.or_not()).map(|(tok, ret)| {
            Expr::Return(tok, ret.map(Recursive::new))
        }),
        Break::parser().then(expr.or_not()).map(|(tok, ret)| {
            Expr::Break(tok, ret.map(Recursive::new))
        }),
    }
}

impl AstParse for LetStmt {
    fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>() -> impl OvalParser<'src, I, Self, E> {
        static_parser! {
            Let::parser()
                .then(Mut::parser().or_not())
                .then(Ident::parser())
                .then(Colon::parser().then(Type::parser()).or_not())
                .then(Equals::parser().then(Expr::parser()).or_not())
                .then(Semicolon::parser())
                .map(|(((((kw_let, kw_mut), name), ty), assignment), semicolon)| {
                    LetStmt {
                        kw_let,
                        kw_mut,
                        name,
                        ty,
                        assignment,
                        semicolon,
                    }
                })
        }
    }
}

impl AstParse for Block {
    fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>() -> impl OvalParser<'src, I, Self, E> {
        // I favor making block unsized rather than expr
        // because expr's parser runs a LOT more
        static_unsized_parser! {
            // handle parsing stmt expressions properly

            let no_block_expr = const { expr_without_block_parser() };

            let stmt_expr = chumsky::primitive::choice((
                no_block_expr.then(Semicolon::parser().map(Some)),
                expr_with_block_parser().then(Semicolon::parser().or_not()),
            ));


            let stmt = chumsky::primitive::choice((
                LetStmt::parser().map(Stmt::Let),
                stmt_expr.map(|(expr, semi)| {
                    Stmt::Expression {
                        expr,
                        trailing: semi
                    }
                }),
                recursive_parser::<Item, _, _>().map(|item| {
                    Stmt::Item(Recursive::new(item))
                }),
            ));

            let padding = Semicolon::parser()
                .ignored()
                .repeated();

            let stmt = padding.ignore_then(stmt).then_ignore(padding);

            stmt
                .repeated()
                .collect::<Vec<_>>()
                .then(no_block_expr.or_not())
                .map(|(mut stmts, expr)| {
                    if let Some(trailing) = expr {
                        stmts.push(Stmt::Expression {
                            expr: trailing,
                            trailing: None
                        })
                    }

                    stmts
                })
                .in_curly_brackets()
                .recover_with(recover_nested_delimiters())
                .map(|stmts| {
                    Block {
                        stmts
                    }
                })
        }
    }
}

impl AstParse for Type {
    fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>()
    -> impl OvalParser<'src, I, Self, E> {
        static_parser! {
            let ty = recursive_parser::<Type, I, E>();

            let fn_ty_args = Ident::parser()
                .then(Colon::parser())
                .or_not()
                .ignore_then(ty)
                .separated_by(Comma::parser())
                .allow_trailing()
                .collect::<Vec<_>>();

            let fn_ty_parser = parse_group((
                Fn::parser(),
                fn_ty_args.in_parens(),
                Arrow::parser().then(ty).or_not()
            ))
                .map(|(kw_fn, args, ret)| Type::Fn(Recursive::new((kw_fn, args, ret))));

            let list_parser = ty
                .then(Semicolon::parser().then(Expr::parser()).or_not())
                .in_square_brackets()
                .map(|list| {
                    let span = list.span();
                    let (list_ty, expr) = list.0;

                    match expr {
                        Some((colon, expr)) => {
                            let array = SquareBracket::new(
                                (list_ty, colon, expr),
                                span
                            );

                            Type::Array(Recursive::new(array))
                        },
                        None => Type::List(Recursive::new(
                            SquareBracket::new(list_ty, span)
                        )),
                    }
                });

            chumsky::primitive::choice((
                Not::parser().map(Type::Never),
                Ident::parser().map(Type::Ident),
                fn_ty_parser,
                ty.recursive_tuple(Type::Parens, Type::Tuple),
                list_parser
            ))
        }
    }
}

impl AstParse for FunctionSignature {
    fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>() -> impl OvalParser<'src, I, Self, E> {
        let arg = parse_group((
            Ident::parser(),
            Colon::parser(),
            Type::parser(),
        ));

        let args = arg
            .separated_by(Comma::parser())
            .allow_trailing()
            .collect::<Vec<_>>()
            .in_parens();


        let func = parse_group((
            Pub::parser().or_not(),
            Extern::parser().or_not(),
            Fn::parser(),
            Ident::parser(),
            args,
            Arrow::parser().then(Type::parser()).or_not(),
        ));

        func.map(|(kw_pub, kw_extern, kw_fn, name, args, ret)| FunctionSignature {
            kw_pub,
            kw_extern,
            kw_fn,
            name,
            args,
            ret,
        })
    }
}

impl AstParse for Function {
    fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>()
        -> impl OvalParser<'src, I, Self, E>
    {
        static_parser! {
            let parser = FunctionSignature::parser().then(chumsky::primitive::choice((
                Block::parser(),
                Semicolon::parser().map_with(|semi, with| {
                    let span = semi.span();
                    let state: &mut SimpleState<ParserState<E::Error>> = with.state();
                    let state: &mut ParserState<E::Error> = state;
                    state.produced_errors.push(E::Error::custom(
                        span,
                        "free function without a body",
                        "missing function body"
                    ));

                    let body = vec![
                        Stmt::Expression {
                            expr: Expr::Error(span),
                            trailing: None
                        }
                    ];

                    Block {
                        stmts: CurlyBrace::new(body, span),
                    }
                }),
            )));

            parser.map(|(signature, body)| Function {
                signature,
                body
            })
        }
    }
}

impl AstParse for ConstItem {
    fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>() -> impl OvalParser<'src, I, Self, E> {
        static_parser! {
            let item = parse_group((
                Pub::parser().or_not(),
                Extern::parser().or_not(),
                Const::parser(),
                Ident::parser(),
                Colon::parser(),
                Type::parser(),
                Equals::parser().then(Expr::parser()).or_not(),
                Semicolon::parser(),
            ));

            item.map_with(|(kw_pub, kw_extern, kw_const, name, colon, ty, assign, semi), extra| {
                let (equals, expr) = match assign {
                    Some((equals, expr)) => (equals, expr),
                    None => {
                        let item_span: Span = extra.span();
                        let state: &mut SimpleState<ParserState<E::Error>> = extra.state();
                        let state: &mut ParserState<E::Error> = state;

                        let name = state.interner.resolve(name.symbol());
                        state.produced_errors.push(E::Error::custom(
                            item_span,
                            "free constant item without body",
                            format_args!("constant `{name}` must have a value")
                        ));

                        let span = semi.span();
                        let equals = Equals::from_token(Token {
                            span,
                            kind: TokenKind::Equals,
                        });
                        let expr = Expr::Error(span);

                        (equals, expr)
                    }
                };

                ConstItem {
                    kw_pub,
                    kw_extern,
                    kw_const,
                    name,
                    ty_colon: colon,
                    ty,
                    eq_token: equals,
                    assignment: expr,
                    semicolon: semi,
                }
            })
        }
    }
}

impl AstParse for Item {
    fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>()
    -> impl OvalParser<'src, I, Self, E> {
        static_parser! {
            chumsky::primitive::choice((
                Function::parser().map(Item::Function),
                ConstItem::parser().map(Item::Const)
            ))
        }
    }
}

impl AstParse for OvalModule {
    fn parser<'src, I: InputTape<'src>, E: ParserData<'src, I>>() -> impl OvalParser<'src, I, Self, E> {
        static_parser! {
            Item::parser()
                .repeated()
                .collect::<Vec<_>>()
                .map(|items| OvalModule { items })
        }
    }
}
