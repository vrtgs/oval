use crate::alloc_helper::{make_slice, slice, RcSlice};
use crate::arena::{make_handle, make_handle_raw, AnyInterner, Arena, ArenaMap, ArenaSlot, HandleInt, IndexMap, SparseArenaMap, SparseArenaMapBuilder, Storable};
use crate::ast::recursive::Recursive;
use crate::ast::{BinOpKind, IntTy, Item, LetStmt, OvalModule, UnOp, UnOpExpr, UnOpKind};
use crate::bitset::BitSet;
use crate::compile::algorithms::topo_sort_dependencies;
use crate::compile::CompileError;
use crate::hashed::HashMap;
use crate::interner::{Interner, Symbol};
use crate::spanned::{spanned_struct, Span, Spanned};
use crate::tokens::Ident;
use crate::{alloc_helper, ast, hashed, recurse};
use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::cmp::Ordering;
use core::fmt::{Debug, Display, Formatter};
use core::hash::Hash;
use core::ops::{Deref, DerefMut, Index};

#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum LiteralValue {
    Integer {
        negative: bool,
        value: u128,
        ty: Option<IntTy>,
    },
    Str(Symbol),
    Char(char),
    Bool(bool),
}

impl From<ast::LiteralValue> for LiteralValue {
    fn from(value: ast::LiteralValue) -> Self {
        match value {
            ast::LiteralValue::Integer { value, suffix, radix: _ } => {
                LiteralValue::Integer { negative: false, value, ty: suffix }
            },
            ast::LiteralValue::Str(val) => LiteralValue::Str(val),
            ast::LiteralValue::Char(val) => LiteralValue::Char(val),
            ast::LiteralValue::Bool(val) => LiteralValue::Bool(val),
        }
    }
}

impl IntTy {
    pub const fn id(self) -> IndirectTyId {
        match self {
            IntTy::Usize => IndirectTyId::USIZE,
            IntTy::U64 => IndirectTyId::U64,
            IntTy::U32 => IndirectTyId::U32,
            IntTy::U16 => IndirectTyId::U16,
            IntTy::U8 => IndirectTyId::U8,

            IntTy::Isize => IndirectTyId::ISIZE,
            IntTy::I64 => IndirectTyId::I64,
            IntTy::I32 => IndirectTyId::I32,
            IntTy::I16 => IndirectTyId::I16,
            IntTy::I8 => IndirectTyId::I8,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
pub enum PrimTy {
    Never,
    Int(IntTy),
    Bool,
}

impl PrimTy {
    pub const USIZE: Self = Self::Int(IntTy::Usize);
    pub const U64: Self = Self::Int(IntTy::U64);
    pub const U32: Self = Self::Int(IntTy::U32);
    pub const U16: Self = Self::Int(IntTy::U16);
    pub const U8: Self = Self::Int(IntTy::U8);

    pub const ISIZE: Self = Self::Int(IntTy::Isize);
    pub const I64: Self = Self::Int(IntTy::I64);
    pub const I32: Self = Self::Int(IntTy::I32);
    pub const I16: Self = Self::Int(IntTy::I16);
    pub const I8: Self = Self::Int(IntTy::I8);

    pub const fn id(self) -> IndirectTyId {
        match self {
            PrimTy::Never => IndirectTyId::NEVER,
            PrimTy::Int(int) => int.id(),
            PrimTy::Bool => IndirectTyId::BOOL
        }
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            PrimTy::Never => "!",
            PrimTy::Int(int) => int.as_str(),
            PrimTy::Bool => "bool",
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum InferKind {
    Any,
    Int,
}

#[derive(Clone)]
pub enum InferTy {
    Infer(InferKind, Span),
    Primitive(PrimTy),
    Tuple(RcSlice<IndirectTyId>),
    List(IndirectTyId),
    Array(IndirectTyId, ConstEvalId),
    Fn(RcSlice<IndirectTyId>, IndirectTyId),
    Error
}

impl InferTy {
    fn is_never(&self) -> bool {
        matches!(*self, InferTy::Primitive(PrimTy::Never))
    }
}

make_handle! {
    pub IndirectTyId for InferTy: Sized;
    with constants {
        pub NEVER = InferTy::Primitive(PrimTy::Never);

        pub USIZE = InferTy::Primitive(PrimTy::USIZE);
        pub U64 = InferTy::Primitive(PrimTy::U64);
        pub U32 = InferTy::Primitive(PrimTy::U32);
        pub U16 = InferTy::Primitive(PrimTy::U16);
        pub U8 = InferTy::Primitive(PrimTy::U8);

        pub ISIZE = InferTy::Primitive(PrimTy::ISIZE);
        pub I64 = InferTy::Primitive(PrimTy::I64);
        pub I32 = InferTy::Primitive(PrimTy::I32);
        pub I16 = InferTy::Primitive(PrimTy::I16);
        pub I8 = InferTy::Primitive(PrimTy::I8);

        pub BOOL = InferTy::Primitive(PrimTy::Bool);

        pub UNIT = InferTy::Tuple(RcSlice::empty());

        pub ERROR = InferTy::Error;
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum ConstExpr {
    ArrayLen(usize, Span),
    LateInit {
        locals: Option<LocalStoreId>,
        expr: ExprId,
    },
}

pub struct ConstExprFull {
    pub decl_span: Span,
    pub ty: IndirectTyId,
    pub ty_span: Span,
    pub expr: ConstExpr
}

impl ConstExprFull {
    pub fn get_span(&self, exprs: &Arena<SpannedExpr>) -> Span {
        match self.expr {
            ConstExpr::ArrayLen(_, spn) => spn,
            ConstExpr::LateInit { locals: _, expr } => exprs[expr].span,
        }
    }
}

make_handle! { pub ConstEvalId for ConstExprFull: Sized; }


#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ConstValue {
    pub span: Span,
    pub eval_id: ConstEvalId,
}

pub struct ConstantsEngine {
    exprs: Arena<ConstExprFull>,
}

impl ConstantsEngine {
    fn new() -> Self {
        Self {
            exprs: Arena::new(),
        }
    }

    pub fn add_length(&mut self, span: Span, usize: usize) -> ConstEvalId {
        self.exprs.store(ConstExprFull {
            decl_span: span,
            ty: IndirectTyId::USIZE,
            ty_span: span,
            expr: ConstExpr::ArrayLen(usize, span),
        })
    }

    pub fn add(
        &mut self,
        span: Span,
        ty: IndirectTyId,
        ty_span: Option<Span>,
        locals: Option<LocalStoreId>,
        expr: ExprId,
    ) -> ConstEvalId {
        self.exprs.store(ConstExprFull {
            decl_span: span,
            ty,
            ty_span: ty_span.unwrap_or(span),
            expr: ConstExpr::LateInit {
                locals,
                expr
            }
        })
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.exprs.len()
    }

    #[inline]
    pub fn count(&self) -> HandleInt {
        self.exprs.count()
    }


    #[inline]
    pub fn iter(&self) -> impl DoubleEndedIterator<Item=(ConstEvalId, &ConstExprFull)> + '_ {
        self.exprs.iter()
    }

    #[inline]
    pub fn keys(&self) -> impl DoubleEndedIterator<Item=ConstEvalId> + use<> {
        self.exprs.keys()
    }

    #[inline]
    pub fn make_side_table<V>(&self) -> ArenaMap<ConstEvalId, V> {
        self.exprs.make_side_table()
    }
}

impl Index<ConstEvalId> for ConstantsEngine {
    type Output = ConstExprFull;

    fn index(&self, index: ConstEvalId) -> &Self::Output {
        &self.exprs[index]
    }
}


mod unification_table;

struct CastConstraint {
    span: ConstraintSpan,
    from: SpannedTy,
    to: SpannedTy
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct ConstConstraint([ConstEvalId; 2]);


impl ConstConstraint {
    pub fn ids_equal(self) -> [ConstEvalId; 2] {
        self.0
    }
}


make_handle_raw!(pub ConstConstraintId);

impl Storable for ConstConstraint {
    type Handle = ConstConstraintId;
}


pub struct InferenceEngine {
    types: Arena<InferTy>,
    table: unification_table::UnificationTableBuilder,
    equal_constants: IndexMap<ConstConstraint, ConstraintSpan>,
    casts: Vec<CastConstraint>,
}

pub enum Coersion {
    NeverToAny,
    ArrayToSlice
}

pub struct TyCheckCtx<'a> {
    interner: &'a mut Interner,
    errors: &'a mut Vec<CompileError>,
    consts: &'a ConstantsEngine,
    funcs: &'a Arena<FuncDef>,
}

impl InferenceEngine {
    pub fn new() -> Self {
        Self {
            types: Arena::new(),
            table: unification_table::UnificationTableBuilder::new(),
            equal_constants: IndexMap::new(),
            casts: vec![],
        }
    }

    fn find_ty(&mut self, ty_id: IndirectTyId) -> (&mut InferTy, IndirectTyId) {
        let root = self.table.find(ty_id);
        (&mut self.types[root], root)
    }

    fn find_n_tys<const N: usize>(
        &mut self,
        ids: [IndirectTyId; N],
    ) -> Option<([&mut InferTy; N], [IndirectTyId; N])> {
        let table = &mut self.table;
        let roots = ids.map(move |id| table.find(id));
        self.types.get_disjoint_mut(roots).map(|roots_ref| (roots_ref, roots))
    }

    pub fn get_ty(&mut self, id: IndirectTyId) -> &InferTy {
        self.find_ty(id).0
    }

    pub fn fresh_var(&mut self, span: Span) -> IndirectTyId {
        self.types.store(InferTy::Infer(InferKind::Any, span))
    }

    pub fn fresh_int_var(&mut self, span: Span) -> IndirectTyId {
        self.types.store(InferTy::Infer(InferKind::Int, span))
    }

    pub fn mk_tuple(&mut self, types: RcSlice<IndirectTyId>) -> IndirectTyId {
        if types.is_empty() {
            return IndirectTyId::UNIT
        }
        self.types.store(InferTy::Tuple(types))
    }

    pub fn mk_list(&mut self, elem: IndirectTyId) -> IndirectTyId {
        self.types.store(InferTy::List(elem))
    }

    pub fn mk_array(&mut self, elem: IndirectTyId, len: ConstEvalId) -> IndirectTyId {
        self.types.store(InferTy::Array(elem, len))
    }

    pub fn mk_fn(&mut self, args: RcSlice<IndirectTyId>, ret: IndirectTyId) -> IndirectTyId {
        self.types.store(InferTy::Fn(args, ret))
    }

    fn assert_constants_eq(&mut self, loc: ConstraintSpan, len_a: ConstEvalId, len_b: ConstEvalId) {
        // sort the lengths so that a == b and b == a show up as the same thing
        let sorted = match ConstEvalId::cmp(&len_a, &len_b) {
            Ordering::Equal => return,
            Ordering::Less => [len_a, len_b],
            Ordering::Greater => [len_b, len_a]
        };

        // only insert if the entry doesn't exist already
        let _ = self.equal_constants.try_insert(ConstConstraint(sorted), loc);

    }

    pub fn infer_literal(
        &mut self,
        errors: &mut Vec<CompileError>,
        lit: LiteralValue,
        span: Span
    ) -> IndirectTyId {
        match lit {
            LiteralValue::Bool(_) => IndirectTyId::BOOL,

            LiteralValue::Integer { ty: Some(ty), .. } => ty.id(),
            LiteralValue::Integer { ty: None, .. } => self.fresh_int_var(span),

            _ => {
                errors.push(CompileError::custom(
                    span,
                    "unsupported literal",
                    "this literal kind has no type in the current type system",
                ));
                IndirectTyId::ERROR
            }
        }
    }

    fn unify_inner(
        &mut self,
        loc: ConstraintSpan,
        a: IndirectTyId,
        b: IndirectTyId
    ) -> Result<(), ()> {
        let Some(([ty_a, ty_b], [root_a, root_b])) = self.find_n_tys([a, b]) else {
            // a == b
            return Ok(());
        };

        match (ty_a, ty_b) {
            // filter already errored avoid causing noise
            (InferTy::Error, _) | (_, InferTy::Error) => Ok(()),

            (InferTy::Infer(ka, _), InferTy::Infer(kb, _)) if  *ka == *kb => {
                self.table.union_known_roots(root_a, root_b);
                Ok(())
            },

            | (concrete, to_infer @ InferTy::Infer(InferKind::Any, _))
            | (to_infer @ InferTy::Infer(InferKind::Any, _), concrete)
            | (concrete @ InferTy::Primitive(PrimTy::Int(_)), to_infer @ InferTy::Infer(InferKind::Int, _))
            | (to_infer @ InferTy::Infer(InferKind::Int, _), concrete @ InferTy::Primitive(PrimTy::Int(_))) => {
                to_infer.clone_from(concrete);
                self.table.union_known_roots(root_a, root_b);
                Ok(())
            }

            (InferTy::Primitive(pa), InferTy::Primitive(pb)) if *pa == *pb => Ok(()),

            (InferTy::Tuple(types_a), InferTy::Tuple(types_b)) if types_a.len() == types_b.len() => {
                if !types_a.is_empty() {
                    let (types_a, types_b) = (
                        types_a.clone(),
                        types_b.clone()
                    );

                    recurse(move || {
                        types_a.iter().zip(types_b.iter()).try_for_each(|(&x, &y)| {
                            self.unify_inner(loc, x, y)
                        })
                    })?
                }

                Ok(())
            }

            (&mut InferTy::List(elem_a), &mut InferTy::List(elem_b)) => {
                recurse(move || self.unify_inner(loc, elem_a, elem_b))
            }

            (&mut InferTy::Array(elem_a, len_a), &mut InferTy::Array(elem_b, len_b)) => {
                self.assert_constants_eq(loc, len_a, len_b);
                recurse(move || self.unify_inner(loc, elem_a, elem_b))
            }

            (
                InferTy::Fn(args_a, ret_a),
                InferTy::Fn(args_b, ret_b)
            ) if args_a.len() == args_b.len() => {
                let (args_a, ret_a) = (args_a.clone(), *ret_a);
                let (args_b, ret_b) = (args_b.clone(), *ret_b);
                recurse(move || {
                    assert_eq!(args_a.len(), args_b.len());

                    for (arg_a, arg_b) in args_a.iter().copied().zip(args_b.iter().copied()) {
                        self.unify_inner(loc, arg_a, arg_b)?
                    }

                    self.unify_inner(loc, ret_a, ret_b)
                })
            }

            (_, _) => Err(())
        }
    }

    fn with_ty_display_inner(
        &mut self,
        interner: &mut Interner,
        consts: &ConstantsEngine,
        funcs: &Arena<FuncDef>,
        expected: IndirectTyId,
        found: IndirectTyId,
        func: &mut dyn FnMut(&dyn Display, &dyn Display)
    ) {
        let types = &*self;
        let interner = &*interner;
        let _ = (interner, types, consts, funcs);

        macro_rules! disp {
            ($ty: expr) => {
                display_ty(
                    interner,
                    types,
                    consts,
                    funcs,
                    $ty
                )
            };
        }

        func(&disp!(expected), &disp!(found))
    }

    fn with_ty_display<T>(
        &mut self,
        interner: &mut Interner,
        consts: &ConstantsEngine,
        funcs: &Arena<FuncDef>,
        expected: IndirectTyId,
        found: IndirectTyId,
        func: impl FnOnce(&dyn Display, &dyn Display) -> T
    ) -> T {
        let mut func = Some(func);
        let mut ret = None;
        self.with_ty_display_inner(
            interner,
            consts,
            funcs,
            expected,
            found,
            &mut |a, b| {
                ret = Some(func.take().unwrap()(a, b))
            }
        );
        ret.unwrap()
    }

    fn emmit_error(
        &mut self,
        ctx: &mut TyCheckCtx,
        expected: IndirectTyId,
        found: IndirectTyId,
        func: impl FnOnce(&dyn Display, &dyn Display) -> CompileError
    ) {
        let err = self.with_ty_display(
            ctx.interner,
            ctx.consts,
            ctx.funcs,
            expected,
            found,
            func
        );
        ctx.errors.push(err)
    }

    fn unify_with_indirection(
        &mut self,
        ctx: &mut TyCheckCtx,
        span: ConstraintSpan,
        a: IndirectTyId,
        b: IndirectTyId,
        display: impl FnOnce(&mut Self) -> (IndirectTyId, IndirectTyId),
    ) {
        match self.unify_inner(span, a, b) {
            Ok(()) => (),
            Err(()) => {
                let (display_a, display_b) = display(self);
                self.emmit_error(
                    ctx,
                    display_a,
                    display_b,
                    move |a, b| CompileError::type_mismatch(
                        span,
                        a,
                        b,
                    )
                );
            }
        }
    }

    pub fn assert_equal(
        &mut self,
        ctx: &mut TyCheckCtx,
        span: ConstraintSpan,
        a: IndirectTyId,
        b: IndirectTyId
    ) {
        self.unify_with_indirection(
            ctx,
            span,
            a,
            b,
            |this| {
                let Some(([_, _], [root_a, root_b])) = this.find_n_tys([a, b]) else {
                    unreachable!("{a:?} == {b:?} could not be unified")
                };
                (root_a, root_b)
            }
        )
    }

    #[must_use]
    pub fn coerce(
        &mut self,
        ctx: &mut TyCheckCtx,
        span: ConstraintSpan,
        from: IndirectTyId,
        to: IndirectTyId
    ) -> Option<Coersion> {
        let Some(([from_ty, to_ty], [from, to])) = self.find_n_tys([from, to]) else {
            // from == to
            return None;
        };

        // flip from and to in arguments since expected is to
        // and from is what was found
        match (from_ty, to_ty) {
            (InferTy::Primitive(PrimTy::Never), _)
            | (_, InferTy::Primitive(PrimTy::Never)) => Some(Coersion::NeverToAny),
            (&mut InferTy::Array(arr_elem, _), &mut InferTy::List(list_elem)) => {
                self.unify_with_indirection(
                    ctx,
                    span,
                    list_elem,
                    arr_elem,
                    |_| (to, from)
                );
                Some(Coersion::ArrayToSlice)
            },
            _ => {
                self.unify_with_indirection(
                    ctx,
                    span,
                    to,
                    from,
                    |_| (to, from)
                );
                None
            }
        }
    }

    #[must_use]
    pub fn coerce_spanned(
        &mut self,
        ctx: &mut TyCheckCtx,
        from: SpannedTy,
        to: SpannedTy
    ) -> Option<Coersion> {
        self.coerce(
            ctx,
            ConstraintSpan::with_constraint(from.span, to.span),
            from.id,
            to.id
        )
    }

    /// returns (coersion for each types, concrete type)
    #[must_use]
    pub fn coerce_all(
        &mut self,
        ctx: &mut TyCheckCtx,
        constraint_span: Span,
        tys: &[SpannedTy],
    ) -> (Vec<(usize, Coersion)>, IndirectTyId) {
        if tys.is_empty() {
            return (vec![], self.fresh_var(constraint_span))
        }

        if let &[one] = tys {
            return (vec![], one.id)
        }

        let mut tys = tys
            .iter()
            .copied()
            .enumerate()
            .collect::<Vec<_>>();

        // never should be evaluated/pushed last
        // and list should be pushed first
        // use a stable sort to keep relative order
        tys.sort_by_key(|&(_i, ty)| {
            match self.get_ty(ty.id) {
                InferTy::List(_) => -1_i8,
                InferTy::Primitive(PrimTy::Never) => 1_i8,
                _ => 0_i8
            }
        });

        let mut coersions = vec![];
        let &[(_i, coerce_to), ref tys @ ..] = tys.as_slice() else {
            unreachable!("tys should be non empty at this point")
        };

        for &(i, ty) in tys {
            let ret = self.coerce(
                ctx,
                ConstraintSpan::with_constraint(ty.span, constraint_span),
                ty.id,
                coerce_to.id
            );

            if let Some(coersion) = ret {
                coersions.push((i, coersion))
            }
        }

        (coersions, coerce_to.id)
    }

    /// returns (coersion for args, function call return)
    #[must_use]
    pub fn call_fn(
        &mut self,
        ctx: &mut TyCheckCtx,
        span: Span,
        callee: SpannedTy,
        args: RcSlice<SpannedTy>,
    ) -> (Vec<(usize, Coersion)>, IndirectTyId) {
        let (callee_ty, callee_id) = self.find_ty(callee.id);
        let ret = match *callee_ty {
            InferTy::Fn(ref expected_args, ret)
                if expected_args.len() == args.len() => {
                let expected_args = expected_args.clone();

                let mut args_coerce = vec![];

                for (i, (&arg, &expected)) in args.iter().zip(expected_args.iter()).enumerate() {
                    let coersion = self.coerce(
                        ctx,
                        ConstraintSpan::new(arg.span),
                        arg.id,
                        expected,
                    );

                    if let Some(coersion) = coersion {
                       args_coerce.push((i, coersion))
                    }
                }

                return (args_coerce, ret)
            },
            InferTy::Fn(_, ret) => ret,
            _ => self.fresh_var(callee.span)
        };

        let expected_func = self.mk_fn(args.iter().map(|ty| ty.id).collect(), ret);

        self.assert_equal(
            ctx,
            ConstraintSpan::new(span),
            callee_id,
            expected_func
        );

        (vec![], ret)
    }

    pub fn index(
        &mut self,
        ctx: &mut TyCheckCtx,
        span: Span,
        container: SpannedTy,
        index: SpannedTy,
    ) -> IndirectTyId {
        self.assert_equal(
            ctx,
            ConstraintSpan::with_constraint(index.span, container.span),
            IndirectTyId::USIZE,
            index.id
        );

        let (container_ty, container_id) = self.find_ty(container.id);
        match *container_ty {
            InferTy::List(elem) => elem,
            InferTy::Array(elem, _) => elem,
            _ => {
                let elem = self.fresh_var(container.span);
                let list = self.mk_list(elem);
                self.assert_equal(ctx, ConstraintSpan::new(span), container_id, list);
                elem
            }
        }
    }

    fn assert_cast_inner(
        &mut self,
        ctx: &mut TyCheckCtx,
        lazy: bool,
        span: ConstraintSpan,
        from: SpannedTy,
        to: SpannedTy
    ) {
        let Some(([from_ty, to_ty], [from_id, to_id])) = self.find_n_tys([from.id, to.id]) else {
            // from == to
            return;
        };

        let from = SpannedTy { id: from_id, span: from.span };
        let to = SpannedTy { id: to_id, span: to.span };

        match *to_ty {
            _ if !matches!(*to_ty, InferTy::Infer(..)) && !matches!(*from_ty, InferTy::Infer(..)) => (),
            _ => match lazy {
                false => self.assert_equal(
                    ctx,
                    span,
                    from_id,
                    to_id
                ),
                true => self.casts.push(CastConstraint {
                    span,
                    from,
                    to,
                }),
            }
        }
    }

    pub fn assert_casts(
        &mut self,
        ctx: &mut TyCheckCtx,
        span: ConstraintSpan,
        from: SpannedTy,
        to: SpannedTy
    ) {
        self.assert_cast_inner(
            ctx,
            /* lazy */ true,
            span,
            from,
            to
        )
    }
}


impl InferenceEngine {
    #[allow(clippy::wrong_self_convention)]
    fn is_never(&mut self, id: IndirectTyId) -> bool {
        id == IndirectTyId::NEVER || self.get_ty(id).is_never()
    }
}


#[derive(Debug, Eq, PartialEq, Hash)]
pub enum Ty {
    Primitive(PrimTy),
    Tuple(Box<[TyId]>),
    List(TyId),
    Array(TyId, ConstEvalId),
    Fn(Box<[TyId]>, TyId),
}

make_handle! {
    pub TyId for Ty: Sized;
    internable;
    with constants {
        pub NEVER = Ty::Primitive(PrimTy::Never);

        pub USIZE = Ty::Primitive(PrimTy::USIZE);
        pub U64 = Ty::Primitive(PrimTy::U64);
        pub U32 = Ty::Primitive(PrimTy::U32);
        pub U16 = Ty::Primitive(PrimTy::U16);
        pub U8 = Ty::Primitive(PrimTy::U8);

        pub ISIZE = Ty::Primitive(PrimTy::ISIZE);
        pub I64 = Ty::Primitive(PrimTy::I64);
        pub I32 = Ty::Primitive(PrimTy::I32);
        pub I16 = Ty::Primitive(PrimTy::I16);
        pub I8 = Ty::Primitive(PrimTy::I8);

        pub BOOL = Ty::Primitive(PrimTy::Bool);

        pub UNIT = Ty::Tuple(alloc_helper::empty_slice());
    }
}

#[derive(Copy, Clone)]
pub struct ConstraintSpan([Span; 2]);

#[derive(Debug)]
pub enum ConstraintSpanRepr {
    Constrained {
        source: Span,
        constraint: Span,
    },
    Single(Span),
}

impl ConstraintSpan {
    pub fn with_constraint(source: Span, constraint: Span) -> Self {
        Self([source, constraint])
    }

    pub fn new(one: Span) -> Self {
        Self([one; 2])
    }

    pub fn get(&self) -> ConstraintSpanRepr {
        let [source, constraint] = self.0;
        match source == constraint {
            true => ConstraintSpanRepr::Single(source),
            false => ConstraintSpanRepr::Constrained {
                source,
                constraint
            }
        }
    }

    pub fn as_two_spans(&self) -> (Span, Option<Span>) {
        match self.get() {
            ConstraintSpanRepr::Single(one) => (one, None),
            ConstraintSpanRepr::Constrained { source, constraint } => {
                (source, Some(constraint))
            }
        }
    }
}


impl Debug for ConstraintSpan {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("MultiSpan").field(&self.get()).finish()
    }
}

pub struct ResolvedTypes {
    pub types: AnyInterner<Ty>,
    pub table: Box<[TyId]>,
    pub equal_constants: IndexMap<ConstConstraint, ConstraintSpan>,
}

impl ResolvedTypes {
    pub fn resolve(&self, ty: IndirectTyId) -> TyId {
        self.table[ty.get()]
    }
}

impl Index<IndirectTyId> for ResolvedTypes {
    type Output = Ty;

    fn index(&self, index: IndirectTyId) -> &Self::Output {
        &self[self.resolve(index)]
    }
}

impl Index<TyId> for ResolvedTypes {
    type Output = Ty;

    fn index(&self, index: TyId) -> &Self::Output {
        &self.types[index]
    }
}

fn topo_sort_types(
    types: &Arena<InferTy>,
    table: &mut unification_table::UnificationTableBuilder,
) -> Vec<IndirectTyId> {
    let deps_cache: Box<[Vec<IndirectTyId>]> = make_slice(
        |index| {
            let ty = IndirectTyId::new(index).unwrap();
            let root = table.find(ty);
            if root != ty {
                return vec![root]
            }

            let mut deps = Vec::new();
            let ty = &types[root];

            let mut push_root = |id: IndirectTyId| {
                let r = table.find(id);
                if r != root {
                    deps.push(r);
                }
            };

            match ty {
                InferTy::Infer(_, _)
                | InferTy::Error
                | InferTy::Primitive(_) => return deps,
                InferTy::Tuple(tys) => {
                    for &t in tys.iter() {
                        push_root(t);
                    }
                }
                InferTy::List(elem) | InferTy::Array(elem, _) => {
                    push_root(*elem);
                }
                InferTy::Fn(args, ret) => {
                    for &a in args.iter() {
                        push_root(a);
                    }
                    push_root(*ret);
                }
            }

            deps
        },
        types.len()
    );

    let res = topo_sort_dependencies::<IndirectTyId, _, ()>(
        types.keys(),
        |stack, node| {
            let iter = deps_cache[node.get()]
                .iter()
                .map(|&id| (id, ()));
            stack.push(iter)
        },
        types.len()
    );
    res.expect("types should never be cyclic")
}


impl InferenceEngine {
    fn solve(
        mut self,
        ctx: &mut TyCheckCtx,
    ) -> Result<ResolvedTypes, ()> {
        for cast in core::mem::take(&mut self.casts) {
            self.assert_cast_inner(
                ctx,
                /* lazy */ false,
                cast.span,
                cast.from,
                cast.to
            )
        }

        let mut contains_errors = false;
        for (id, ty) in self.types.iter_mut() {
            if id == IndirectTyId::ERROR {
                continue
            }
            contains_errors |= matches!(ty, InferTy::Error);
            if let InferTy::Infer(kind, span) = *ty {
                *ty = match kind {
                    InferKind::Any => {
                        ctx.errors.push(CompileError::custom(
                            span,
                            "can't infer",
                            "could not infer type of expression"
                        ));
                        contains_errors = true;
                        InferTy::Error
                    },
                    InferKind::Int => InferTy::Primitive(PrimTy::I32),
                }
            }
        }

        if contains_errors {
            return Err(())
        }

        let Self {
            types,
            mut table,
            equal_constants,
            casts,
        } = self;

        assert!(casts.is_empty());

        #[cfg(debug_assertions)]
        let mut root_initialized = BitSet::new(types.len());

        let mut real_ty = slice![TyId::UNIT; types.len()];

        let types_ord = topo_sort_types(
            &types,
            &mut table
        );

        let mut new_types = AnyInterner::new();

        for id in types_ord {
            let get_root_ty = |root: IndirectTyId| {
                #[cfg(debug_assertions)]
                {
                    assert!(root_initialized.get(root.get()), "root {root:?} not initialized")
                }
                real_ty[root.get()]
            };

            let root_id = table.find(id);
            if root_id != id {
                let root_ty = get_root_ty(root_id);
                real_ty[id.get()] = root_ty;
                // queries only hit roots so no need to set root_initialized
                continue;
            }

            let mut get_real_ty = |ty_id: IndirectTyId| {
                let root = table.find(ty_id);
                get_root_ty(root)
            };

            let real_ty_id = match types[id] {
                InferTy::Primitive(PrimTy::Never) => TyId::NEVER,

                InferTy::Primitive(PrimTy::USIZE) => TyId::USIZE,
                InferTy::Primitive(PrimTy::U64) => TyId::U64,
                InferTy::Primitive(PrimTy::U32) => TyId::U32,
                InferTy::Primitive(PrimTy::U16) => TyId::U16,
                InferTy::Primitive(PrimTy::U8) => TyId::U8,

                InferTy::Primitive(PrimTy::ISIZE) => TyId::ISIZE,
                InferTy::Primitive(PrimTy::I64) => TyId::I64,
                InferTy::Primitive(PrimTy::I32) => TyId::I32,
                InferTy::Primitive(PrimTy::I16) => TyId::I16,
                InferTy::Primitive(PrimTy::I8) => TyId::I8,

                InferTy::Primitive(PrimTy::Bool) => TyId::BOOL,

                InferTy::Tuple(ref tup) if tup.is_empty() => TyId::UNIT,
                InferTy::Tuple(ref tup) => {
                    let tup = tup
                        .iter()
                        .copied()
                        .map(get_real_ty)
                        .collect();
                    new_types.get_or_intern(Ty::Tuple(tup))
                },
                InferTy::List(elem) => {
                    new_types.get_or_intern(Ty::List(get_real_ty(elem)))
                }
                InferTy::Array(elem, len) => {
                    new_types.get_or_intern(Ty::Array(get_real_ty(elem), len))
                }
                InferTy::Fn(ref args, ret) => {
                    let args = args
                        .iter()
                        .copied()
                        .map(&mut get_real_ty)
                        .collect();
                    new_types.get_or_intern(Ty::Fn(args, get_real_ty(ret)))
                }
                InferTy::Infer(_, _) => unreachable!(),
                InferTy::Error => {
                    assert_eq!(id, IndirectTyId::ERROR);
                    TyId::UNIT
                },
            };

            real_ty[id.get()] = real_ty_id;
            #[cfg(debug_assertions)]
            {
                root_initialized.set(id.get())
            }
        }

        Ok(ResolvedTypes {
            types: new_types,
            table: real_ty,
            equal_constants,
        })
    }
}

#[derive(Copy, Clone)]
pub struct SpannedTy {
    pub id: IndirectTyId,
    pub span: Span
}

spanned_struct!(SpannedTy);

pub struct LocalDef {
    pub name: Symbol,
    pub ty: Option<SpannedTy>,
    pub mutable: bool,
}

make_handle! { pub LocalId for LocalDef: Sized; }

pub type LocalStorage = Arena<LocalDef>;

make_handle! { pub LocalStoreId for LocalStorage: Sized; }

pub enum Stmt {
    Expression {
        expr: ExprId,
        /// if `is_expr_stmt` then expr **MUST** return TyId::UNIT
        is_expr_stmt: bool,
    },
    Let {
        local: LocalId,
        initializer: Option<ExprId>,
        span: Span,
    }
}

#[derive(Copy, Clone)]
pub enum TrailingExpr {
    Trailing(ExprId),
    FallbackUnit(ExprId),
}

pub struct Block {
    pub stmts: Vec<Stmt>,
    pub trailing_expr: TrailingExpr,
}

#[derive(Debug, Copy, Clone)]
pub struct IfBranch {
    pub condition: ExprId,
    pub body: BlockId,
}

#[derive(Copy, Clone)]
pub enum Resource {
    Global(DefId),
    Local(LocalId),
}

pub enum Expr {
    Error,
    Literal(LiteralValue),
    Const(ConstDefId),
    Function(FuncId),
    Local(LocalId),
    Assign { location: ExprId, expr: ExprId },
    BinOp { lhs: ExprId, op: BinOpKind, rhs: ExprId },
    UnOp { op: UnOpKind, expr: ExprId },
    CastAs { expr: ExprId, to: SpannedTy },
    Call { callee: ExprId, args: Vec<ExprId> },
    Index { container: ExprId, index: ExprId },
    Tuple(Vec<ExprId>),
    ArraySplat {
        element: ExprId,
        len: ConstValue,
    },
    Array(Vec<ExprId>),
    Return(ExprId),
    Break(ExprId),
    Continue,
    Block(BlockId),
    Loop(BlockId),
    If {
        if_so: IfBranch,
        else_if: Vec<IfBranch>,
        else_branch: Option<BlockId>,
    }
}

pub struct SpannedExpr {
    pub span: Span,
    pub expr: Expr,
}

spanned_struct!(SpannedExpr);

make_handle! { pub ExprId for SpannedExpr: Sized; }
make_handle! { pub BlockId for Block: Sized; }


#[derive(Debug)]
pub struct FuncDef {
    pub signature: Span,
    pub ret_ty_span: Span,
    pub ty: IndirectTyId,
    pub name: Ident,
    pub args: Vec<LocalId>,
    pub duplicate_args: Option<BitSet>,
    pub local_store: Option<LocalStoreId>,
    pub is_const: bool,
    pub body: ExprId,
}

make_handle!(pub FuncId for Option<FuncDef>: Sized;);

impl Storable for FuncDef {
    type Handle = FuncId;
}

pub struct ConstDef {
    pub name: Ident,
    pub span: Span,
    pub value: ConstEvalId,
}

make_handle!(pub ConstDefId for Option<ConstDef>: Sized;);

impl Storable for ConstDef {
    type Handle = ConstDefId;
}

#[derive(Copy, Clone)]
pub enum Def {
    Const(ConstDefId),
    Function(FuncId),
}

make_handle! { pub DefId for Def: Sized; }

#[derive(Copy, Clone)]
pub enum TypeDef {
    Primitive(PrimTy),
}

pub struct GlobalScope {
    declarations_in_scope: hashed::PersistentHashMap<Symbol, DefId>,
    type_scope: hashed::PersistentHashMap<Symbol, TypeDef>
}

impl GlobalScope {
    pub fn resolve_val(&self, symbol: Symbol) -> Option<DefId> {
        self.declarations_in_scope.get(&symbol).cloned()
    }

    pub fn resolve_type(&self, symbol: Symbol) -> Option<IndirectTyId> {
        self.type_scope.get(&symbol).copied().map(|TypeDef::Primitive(ty)| ty.id())
    }
}

struct GlobalScopeBuilder<'a> {
    this_scope: GlobalScopeId,
    declarations_in_scope: hashed::PersistentHashMap<Symbol, DefId>,
    type_scope: hashed::PersistentHashMap<Symbol, TypeDef>,
    local_declarations: HashMap<Symbol, Span>,
    slot: ArenaSlot<'a, GlobalScope>,
}

impl GlobalScopeBuilder<'_> {
    pub fn id(&self) -> GlobalScopeId {
        self.this_scope
    }

    pub fn insert(&mut self, ident: Ident, id: DefId) -> Result<(), Span> {
        match self.local_declarations.try_insert(ident.symbol, ident.span) {
            Ok(_) => {
                self.declarations_in_scope.insert_mut(ident.symbol, id);
                Ok(())
            }
            Err(occ) => Err(*occ.entry.get())
        }
    }

    pub fn build(self) -> GlobalScopeId {
        self.slot.insert(GlobalScope {
            declarations_in_scope: self.declarations_in_scope,
            type_scope: self.type_scope
        });

        self.this_scope
    }
}

impl GlobalScope {
    fn sub_scope(
        id: GlobalScopeId,
        arena: &mut Arena<GlobalScope>
    ) -> GlobalScopeBuilder<'_> {
        let this = &arena[id];
        let declarations = this.declarations_in_scope.clone();
        let type_scope = this.type_scope.clone();
        let (this_scope, slot) = arena.reserve();

        GlobalScopeBuilder {
            this_scope,
            declarations_in_scope: declarations,
            type_scope,
            local_declarations: HashMap::default(),
            slot
        }
    }
}

// FIXME better type scoping

make_handle! {
    pub GlobalScopeId for GlobalScope: Sized;

    with constants {
        ROOT = GlobalScope {
            declarations_in_scope: hashed::ph_map! { },
            type_scope: hashed::ph_map! {
                Symbol::USIZE => TypeDef::Primitive(PrimTy::USIZE),
                Symbol::U64 => TypeDef::Primitive(PrimTy::U64),
                Symbol::U32 => TypeDef::Primitive(PrimTy::U32),
                Symbol::U16 => TypeDef::Primitive(PrimTy::U16),
                Symbol::U8 => TypeDef::Primitive(PrimTy::U8),

                Symbol::ISIZE => TypeDef::Primitive(PrimTy::ISIZE),
                Symbol::I64 => TypeDef::Primitive(PrimTy::I64),
                Symbol::I32 => TypeDef::Primitive(PrimTy::I32),
                Symbol::I16 => TypeDef::Primitive(PrimTy::I16),
                Symbol::I8 => TypeDef::Primitive(PrimTy::I8),

                Symbol::BOOL => TypeDef::Primitive(PrimTy::Bool),
            }
        };
    }
}

pub fn make_ty_str(
    interner: &Interner,
    types: &InferenceEngine,
    consts: &ConstantsEngine,
    funcs: &Arena<FuncDef>,
    id: IndirectTyId,
) -> Cow<'static, str> {
    let _ = (interner, funcs);
    let make_again = move |ty: IndirectTyId| {
        assert_ne!(id, ty);
        make_ty_str(interner, types, consts, funcs, ty)
    };

    let push_rest_args = move |string: &mut String, rest: &[IndirectTyId]| {
        for &ty in rest {
            let str = make_again(ty);
            string.push_str(", ");
            string.push_str(&str);
        }
    };

    let mut string = match types.types[id] {
        InferTy::Infer(InferKind::Any, _) => return Cow::Borrowed("_"),
        InferTy::Infer(InferKind::Int, _) => return Cow::Borrowed("{integer}"),

        InferTy::Primitive(prim) => return Cow::Borrowed(prim.as_str()),

        InferTy::Tuple(ref tuple) => {
            let [first, ref rest @ ..] = **tuple else {
                return Cow::Borrowed("()")
            };

            recurse(|| {
                let mut string = make_again(first).into_owned();
                string.reserve(3); // minimum (,)
                string.insert(0, '(');
                match *rest {
                    [] => string.push_str(",)"),
                    _ => {
                        push_rest_args(&mut string, rest);
                        string.push(')');
                    }
                }

                string
            })
        },
        InferTy::List(elem) => recurse(|| {
            let mut str = make_again(elem).into_owned();
            str.reserve(2); // exactly []
            str.insert(0, '[');
            str.push(']');
            str
        }),
        InferTy::Array(elem, _len) => recurse(|| {
            let mut str = make_again(elem).into_owned();
            str.reserve(4); // for "[; _]"
            str.insert(0, '[');
            str.push_str("; _]");
            str
        }),
        InferTy::Fn(ref args, ret) => {
            let ret = recurse(|| {
                let base = match **args {
                    [] => Cow::Borrowed("fn()"),
                    [first, ref rest @ ..] => {
                        let mut string = make_again(first).into_owned();
                        string.reserve(4); // minimum "fn()"
                        string.insert_str(0, "fn(");
                        push_rest_args(&mut string, rest);
                        string.push(')');
                        Cow::Owned(string)
                    }
                };

                match types.types[ret] {
                    InferTy::Tuple(ref tup) if tup.is_empty() => base,
                    _ => Cow::Owned(base.into_owned() + " -> " + &*make_again(ret))
                }
            });

            match ret {
                ret @ Cow::Borrowed(_) => return ret,
                Cow::Owned(str) => str,
            }
        },
        InferTy::Error => return Cow::Borrowed("ERROR"),
    };

    const CUTOFF: usize = 512;

    if string.len() > CUTOFF {
        let replacement = "...";
        let mut cutoff = CUTOFF - replacement.len();

        while !string.is_char_boundary(cutoff) {
            cutoff -= 1;
        }

        string.truncate(cutoff);
        string.push_str(replacement);
    }

    Cow::Owned(string)
}

pub fn display_ty<'a>(
    interner: &'a Interner,
    types: &'a InferenceEngine,
    consts: &'a ConstantsEngine,
    funcs: &'a Arena<FuncDef>,
    ty: IndirectTyId
) -> impl Display + use<'a> {
    struct DisplayTy<'a> {
        interner: &'a Interner,
        types: &'a InferenceEngine,
        consts: &'a ConstantsEngine,
        funcs: &'a Arena<FuncDef>,
        ty: IndirectTyId
    }

    impl Display for DisplayTy<'_> {
        fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
            f.write_str(&make_ty_str(
                self.interner,
                self.types,
                self.consts,
                self.funcs,
                self.ty
            ))
        }
    }

    DisplayTy {
        interner,
        types,
        consts,
        funcs,
        ty
    }
}


struct HirBuilder<'ast, 'b> {
    scopes: Arena<GlobalScope>,
    definitions: Arena<Def>,
    functions: Arena<Option<FuncDef>>,
    consts: Arena<Option<ConstDef>>,
    local_storages: Arena<LocalStorage>,
    exprs: Arena<SpannedExpr>,
    blocks: Arena<Block>,
    const_exprs: ConstantsEngine,
    types: InferenceEngine,
    analysis_stack: Vec<(DefId, GlobalScopeId, &'ast Item)>,
    interner: &'b mut Interner,
    compile_errors: &'b mut Vec<CompileError>,
}

#[derive(Debug, Copy, Clone)]
enum ParsingContext {
    Function,
    Constant
}

type LocalsDataMap = hashed::PersistentHashMap<Symbol, (LocalStoreId, LocalId)>;

// when the map is inherited; the store isn't this just means
// things like let x = 0; const { x }; do resolve
// but cause compile errors
enum LocalsDataStorage {
    Fresh,
    InheritedMap(LocalsDataMap),
    Init {
        current_store: LocalStoreId,
        map: LocalsDataMap
    }
}

enum LocalsState<'a> {
    Owned(LocalsDataStorage),
    Inherited(&'a mut LocalsDataStorage),
}

struct BuilderLocalsData<'a> {
    // None when no locals have been defined yet
    // when locals get defined it is set to Some
    state: LocalsState<'a>,
    context: ParsingContext,
}

impl BuilderLocalsData<'_> {
    fn storage(&mut self) -> &mut LocalsDataStorage {
        match self.state {
            LocalsState::Inherited(ref mut store) => store,
            LocalsState::Owned(ref mut store) => store
        }
    }

    fn locals_data(&mut self) -> (Option<LocalStoreId>, Option<&mut LocalsDataMap>) {
        match *self.storage() {
            LocalsDataStorage::Fresh => (None, None),
            LocalsDataStorage::InheritedMap(ref mut map) => (None, Some(map)),
            LocalsDataStorage::Init { current_store, ref mut map } => {
                (Some(current_store), Some(map))
            }
        }
    }

    fn current_store(&mut self) -> Option<LocalStoreId> {
        self.locals_data().0
    }
}

struct ScopedHirBuilder<'scope, 'builder, 'ast, 'b> {
    global_scope: GlobalScopeId,
    locals: BuilderLocalsData<'scope>,
    builder: &'builder mut HirBuilder<'ast, 'b>
}

impl<'scope, 'builder, 'ast, 'b> ScopedHirBuilder<'scope, 'builder, 'ast, 'b> {
    fn sub_scope_locals<'new_scope>(
        &'new_scope mut self,
        extract_locals: impl FnOnce(&'new_scope mut BuilderLocalsData<'scope>) -> BuilderLocalsData<'new_scope>
    ) -> ScopedHirBuilder<'new_scope, 'new_scope, 'ast, 'b>
    where
        'builder : 'new_scope,
    {
        ScopedHirBuilder {
            global_scope: self.global_scope,
            locals: extract_locals(&mut self.locals),
            builder: self.builder,
        }
    }

    fn new_unit(&mut self, span: Span) -> ExprId {
        self.builder.exprs.store(SpannedExpr {
            span,
            expr: const { Expr::Tuple(vec![]) },
        })
    }

    fn insert_local(&mut self, symbol: Symbol, def: LocalDef) -> LocalId {
        let store_state = self.locals.storage();

        macro_rules! insert_with_map {
            ($store_state: expr, $map: expr $(,)?) => {{
                let map = $map;
                let store_state = $store_state;
                let (handle, slot) = self.builder.local_storages.reserve();
                let storage = slot.insert(LocalStorage::new());

                *store_state = LocalsDataStorage::Init {
                    current_store: handle,
                    map
                };

                storage
            }};
        }

        let storage = match *store_state {
            LocalsDataStorage::Fresh => insert_with_map!(&mut *store_state, LocalsDataMap::default()),
            LocalsDataStorage::InheritedMap(ref map) => {
                let map = (*map).clone();
                insert_with_map!(&mut *store_state, map)
            },
            LocalsDataStorage::Init { current_store, .. } => {
                &mut self.builder.local_storages[current_store]
            }
        };

        let LocalsDataStorage::Init { current_store: store_id, .. } = *store_state else {
            unreachable!()
        };

        if let LocalsState::Inherited(LocalsDataStorage::Init { map, ..}) = self.locals.state {
            let map = (*map).clone();
            self.locals.state = LocalsState::Owned(LocalsDataStorage::Init {
                current_store: store_id,
                map
            });
        }

        let LocalsState::Owned(LocalsDataStorage::Init { ref mut map, .. }) = self.locals.state else {
            unreachable!()
        };

        let (local_id, slot) = storage.reserve();
        map.insert_mut(symbol, (store_id, local_id));
        slot.insert(def);
        local_id
    }


    fn resolve_resource<F: FnOnce(&mut Self, Resource) -> Option<T>, T>(
        &mut self,
        ident: Ident,
        and_then: F
    ) -> Result<Option<T>, ()> {
        if  let (current_store, Some(locals_map)) = self.locals.locals_data()
            && let Some(&(store, local)) = locals_map.get(&ident.symbol)
        {
            if current_store == Some(store) {
                return Ok(and_then(self, Resource::Local(local)))
            }

            let (label, message) = match self.locals.context {
                ParsingContext::Function => {
                    (
                        "can't capture dynamic environment in a fn item",
                        "capture occurs here"
                    )
                }
                ParsingContext::Constant => {
                    (
                        "attempt to use a non-constant value in a constant",
                        "non-constant value"
                    )
                }
            };

            self.builder.compile_errors.push(CompileError::custom(
                ident.span,
                label,
                message
            ));

            return Err(())
        }

        let res = self.builder.scopes[self.global_scope]
            .resolve_val(ident.symbol)
            .map(Resource::Global)
            .and_then(move |id| and_then(self, id));

        Ok(res)
    }

    fn resolve_bin_op(
        &mut self,
        expr1: &'ast ast::Expr,
        expr2: &'ast ast::Expr,
        fold: impl FnOnce(ExprId, ExprId) -> Expr
    ) -> (Span, Expr) {
        let (span1, expr1) = self.resolve_expr_spanned(expr1);
        let (span2, expr2) = self.resolve_expr_spanned(expr2);
        (Span::merge(span1, span2), fold(expr1, expr2))
    }

    fn halt_expr(
        &mut self,
        halt_span: Span,
        expr: &'ast Option<Recursive<ast::Expr>>,
        make: impl FnOnce(ExprId) -> Expr
    ) -> (Span, Expr) {
        match expr {
            Some(expr) => expr.with_inner(|expr| {
                let (span1, expr) = self.resolve_expr_spanned(expr);
                (Span::merge(halt_span, span1), make(expr))
            }),
            None => {
                let unit = self.new_unit(halt_span);
                (halt_span, make(unit))
            }
        }
    }

    fn recurse_resolve_expr_list(
        &mut self,
        list_span: Span,
        exprs: &'ast [ast::Expr],
        make: impl FnOnce(Vec<ExprId>) -> Expr
    ) -> (Span, Expr) {
        let exprs = match exprs {
            [] => vec![],
            exprs => recurse(move || {
                exprs
                    .iter()
                    .map(move |expr| self.resolve_expr(expr))
                    .collect()
            })
        };

        (list_span, make(exprs))
    }

    pub fn resolve_expr_spanned(&mut self, expr: &'ast ast::Expr) -> (Span, ExprId) {
        let (span, expr) = match expr {
            ast::Expr::Parens(inner) => {
                return inner.with_inner(|parn| {
                    let span = parn.span();
                    (span, self.resolve_expr(&parn.0))
                })
            },

            &ast::Expr::Error(spn) => (spn, Expr::Error),
            &ast::Expr::Literal(lit) => (lit.span, Expr::Literal(lit.value.into())),
            &ast::Expr::Ident(ident) => {
                let map = |this: &mut Self, res| Some({
                    match res {
                        Resource::Global(def) => match this.builder.definitions[def] {
                            Def::Const(cnst) => Expr::Const(cnst),
                            Def::Function(func) => Expr::Function(func),
                        }
                        Resource::Local(id) => Expr::Local(id),
                    }
                });
                let expr = match self.resolve_resource(ident, map) {
                    Ok(Some(expr)) => expr,
                    Ok(None) => {
                        self.builder.compile_errors.push(CompileError::val_not_found(
                            ident.span,
                            self.builder.interner.resolve(ident.symbol)
                        ));

                        Expr::Error
                    },
                    Err(()) => Expr::Error,
                };

                (ident.span, expr)
            },
            ast::Expr::Assign(assign) => {
                assign.with_inner(|expr| {
                    self.resolve_bin_op(
                        &expr.location,
                        &expr.expr,
                        |location, expr| Expr::Assign { location, expr }
                    )
                })
            },
            ast::Expr::BinaryOp(bin_op) => {
                bin_op.with_inner(|bin_op| {
                    let op = bin_op.op.kind;
                    self.resolve_bin_op(
                        &bin_op.lhs,
                        &bin_op.rhs,
                        move |lhs, rhs| Expr::BinOp { lhs, op, rhs }
                    )
                })
            }
            ast::Expr::UnaryOp(op) => {
                op.with_inner(|UnOpExpr { op, expr }| {
                    let (expr_span, expr) = self.resolve_expr_spanned(expr);
                    let UnOp { kind, span: op_span } = *op;

                    (Span::merge(op_span, expr_span), Expr::UnOp { op: kind, expr })
                })
            }
            ast::Expr::CastAs(cast_as) => {
                cast_as.with_inner(|cast_as| {
                    let (start_span, expr) = self.resolve_expr_spanned(&cast_as.expr);
                    let to = self.resolve_ty_spanned(&cast_as.ty);
                    (Span::merge(start_span, to.span), Expr::CastAs { expr, to })
                })
            }
            ast::Expr::Call(call) => {
                call.with_inner(|call| {
                    let (callee_span, callee) = self.resolve_expr_spanned(&call.callee);
                    let args = &call.args;
                    let args_paren_span = args.span();
                    let args = &args.0;

                    let args = args
                        .iter()
                        .map(|expr| self.resolve_expr(expr))
                        .collect();

                    (Span::merge(callee_span, args_paren_span), Expr::Call {
                        callee,
                        args,
                    })
                })
            }
            ast::Expr::Index(index) => {
                index.with_inner(|index| {
                    self.resolve_bin_op(
                        &index.container,
                        &index.index.0,
                        |container, index| Expr::Index { container, index }
                    )
                })
            }

            ast::Expr::Tuple(tuple) => {
                let tuple = tuple.get_ref();
                let span = tuple.span();
                self.recurse_resolve_expr_list(
                    span,
                    &tuple.0,
                    Expr::Tuple
                )
            }
            ast::Expr::Array(array) => {
                let array = array.get_ref();
                let span = array.span();
                match &array.0 {
                    ast::ArrayElements::Literal(vec) => {
                        self.recurse_resolve_expr_list(
                            span,
                            vec,
                            Expr::Array
                        )
                    },
                    ast::ArrayElements::Splat { element, kw_dyn, size } => {
                        if kw_dyn.is_some() {
                            todo!("dyn splat")
                        }
                        recurse(|| {
                            let element = self.resolve_expr(element);
                            let len = self.resolve_anynonmous_const_expr(
                                size,
                                IndirectTyId::USIZE,
                            );
                            (span, Expr::ArraySplat {
                                element,
                                len
                            })
                        })
                    }
                }
            }
            ast::Expr::Return(tok, val) => {
                self.halt_expr(tok.span(), val, Expr::Return)
            }
            ast::Expr::Break(tok, val) => {
                self.halt_expr(tok.span(), val, Expr::Break)
            },
            ast::Expr::Continue(tok) => (tok.span(), Expr::Continue),

            // all exprs containing blocks must have recursion guards
            ast::Expr::Block(block) => {
                let (span, id) = block.with_inner(|block| {
                    self.resolve_block_spanned(block)
                });
                (span, Expr::Block(id))
            }
            ast::Expr::Loop(block) => {
                block.with_inner(|loop_expr| {
                    let (span, id) = self.resolve_block_spanned(&loop_expr.body);
                    (Span::merge(loop_expr.kw_loop.span(), span), Expr::Loop(id))
                })
            }
            ast::Expr::If(if_expr) => {
                if_expr.with_inner(|if_expr| {
                    let mut make_branch_with_end = |if_branch: &'ast ast::IfBranch| {
                        let cond = self.resolve_expr(&if_branch.condition);
                        let (end, body) = self.resolve_block_spanned(&if_branch.body);
                        let br = IfBranch {
                            condition: cond,
                            body,
                        };

                        (end, br)
                    };

                    let start = if_expr.first.kw_if.span();
                    let (mut end, if_so) = make_branch_with_end(&if_expr.first);

                    let else_if = if_expr
                        .else_if
                        .iter()
                        .map(|(_else, if_br)| {
                            let (new_end, else_if) = make_branch_with_end(if_br);
                            end = new_end;
                            else_if
                        })
                        .collect();


                    let else_branch = if_expr
                        .else_branch
                        .as_ref()
                        .map(|(_else, block)| {
                            let (new_end, block) = self.resolve_block_spanned(block);
                            end = new_end;
                            block
                        });

                    let expr = Expr::If {
                        if_so,
                        else_if,
                        else_branch
                    };

                    (Span::merge(start, end), expr)
                })
            }
        };

        (span, self.builder.exprs.store(SpannedExpr {
            span,
            expr
        }))
    }

    pub fn resolve_const_expr_inner(
        &mut self,
        expr: &'ast ast::Expr,
        ty: IndirectTyId,
        signature: Option<Span>,
        ty_span: Option<Span>,
    ) -> ConstValue {
        let mut sub_parser = self.sub_scope_locals(|old_locals| {
            BuilderLocalsData {
                context: ParsingContext::Constant,
                state: LocalsState::Owned(match old_locals.locals_data().1 {
                    Some(map) => LocalsDataStorage::InheritedMap((*map).clone()),
                    None => LocalsDataStorage::Fresh,
                }),
            }
        });

        let (span, expr_id) = sub_parser.resolve_expr_spanned(expr);
        let span = signature.unwrap_or(span);
        let local_store = sub_parser.locals.current_store();
        let eval_id = sub_parser.builder.const_exprs.add(
            span,
            ty,
            ty_span,
            local_store,
            expr_id,
        );

        ConstValue {
            span,
            eval_id
        }
    }

    pub fn resolve_anynonmous_const_expr(
        &mut self,
        expr: &'ast ast::Expr,
        ty: IndirectTyId,
    ) -> ConstValue {
        self.resolve_const_expr_inner(expr, ty, None, None)
    }

    pub fn resolve_declared_const_expr(
        &mut self,
        expr: &'ast ast::Expr,
        ty: IndirectTyId,
        signature: Span,
        ty_span: Span,
    ) -> ConstValue {
        self.resolve_const_expr_inner(expr, ty, Some(signature), Some(ty_span))
    }

    pub fn resolve_block_spanned(&mut self, block: &'ast ast::Block) -> (Span, BlockId) {
        let span = block.span();
        let block = match block.stmts.0.as_slice() {
            [] => Block {
                stmts: vec![],
                trailing_expr: TrailingExpr::FallbackUnit(self.new_unit(span)),
            },
            stmts => {
                let (stmts, trailing) = match *stmts {
                    [ref stmts @ .., ast::Stmt::Expression { ref expr, trailing_semicolon: None }] => {
                        (stmts, Some(expr))
                    },
                    ref stmts => (stmts, None)
                };

                let context = self.locals.context;
                let mut sub_parser = self.sub_scope_locals(|old_locals| {
                    BuilderLocalsData {
                        context,
                        state: LocalsState::Inherited(old_locals.storage()),
                    }
                });

                let first_item = stmts.iter().position(|stmt| {
                    matches!(stmt, ast::Stmt::Item(_))
                });

                let mut number_of_items = 0;
                if let Some(first_item) = first_item {
                    let stmts_with_items = &stmts[first_item..];
                    let items = stmts_with_items
                        .iter()
                        .filter_map(|stmt| {
                            match stmt {
                                ast::Stmt::Item(item) => Some(item.get_ref()),
                                _ => None
                            }
                        })
                        .inspect(|_| number_of_items += 1);

                    let scope_id = sub_parser
                        .builder
                        .queue_scope_items(sub_parser.global_scope, items);

                    sub_parser.global_scope = scope_id;
                }


                let capacity = match first_item.is_some() {
                    true => stmts.len() - number_of_items,
                    false => stmts.len()
                };

                let mut new_stmts = Vec::with_capacity(capacity);

                let mut last_drop_cause = span;
                for stmt in stmts {
                    last_drop_cause = match stmt {
                        ast::Stmt::Item(item) => item.span(),
                        ast::Stmt::Expression {
                            expr,
                            trailing_semicolon
                        } => {
                            let (expr_span, expr) = sub_parser.resolve_expr_spanned(expr);
                            new_stmts.push(Stmt::Expression {
                                expr,
                                is_expr_stmt: trailing_semicolon.is_none(),
                            });

                            trailing_semicolon.map_or(
                                expr_span,
                                |semi| semi.span()
                            )
                        }
                        ast::Stmt::Let(let_stmt) => {
                            let LetStmt {
                                kw_let: _,
                                kw_mut,
                                name,
                                ty,
                                assignment,
                                semicolon
                            } = let_stmt;

                            let mutable = kw_mut.is_some();
                            let ty = ty.as_ref().map(|(_colon, ty)| {
                                sub_parser.resolve_ty_spanned(ty)
                            });

                            // resolve the expr **before** inserting local
                            // that way shadowing variables works properly
                            let initializer = assignment
                                .as_ref()
                                .map(|(_eq, expr)| sub_parser.resolve_expr(expr));

                            let local = sub_parser.insert_local(
                                name.symbol,
                                LocalDef {
                                    name: name.symbol,
                                    ty,
                                    mutable,
                                }
                            );

                            new_stmts.push(Stmt::Let {
                                local,
                                initializer,
                                span: let_stmt.span()
                            });

                            semicolon.span()
                        }
                    }
                }

                let trailing = match trailing {
                    Some(expr) => TrailingExpr::Trailing(sub_parser.resolve_expr(expr)),
                    None => TrailingExpr::FallbackUnit(self.new_unit(last_drop_cause))
                };

                Block {
                    stmts: new_stmts,
                    trailing_expr: trailing,
                }
            },
        };

        (span, self.builder.blocks.store(block))
    }

    pub fn resolve_block(&mut self, block: &'ast ast::Block) -> BlockId {
        self.resolve_block_spanned(block).1
    }

    pub fn resolve_ty_spanned(&mut self, ty: &'ast ast::Type) -> SpannedTy {
        let (span, ty) = match ty {
            ast::Type::Parens(ty) => ty.with_inner(|ty| {
                let span = ty.span();
                (span, self.resolve_ty(&ty.0))
            }),

            ast::Type::Tuple(tys) => {
                let tys = tys.get_ref();
                let span = tys.span();
                let tys = tys.0.as_slice();
                match tys {
                    [] => (span, IndirectTyId::UNIT),
                    tys => recurse(|| {
                        let tys = tys
                            .iter()
                            .map(|ty| self.resolve_ty(ty))
                            .collect();

                        (span, self.builder.types.mk_tuple(tys))
                    })
                }
            }

            ast::Type::Never(tok) => (tok.span(), IndirectTyId::NEVER),
            ast::Type::Ident(ident) => {
                let id = 'id: {
                    if let Some(id) = self.builder.scopes[self.global_scope].resolve_type(ident.symbol) {
                        break 'id id
                    }

                    let name = self.builder.interner.resolve(ident.symbol);
                    self.builder.compile_errors.push(CompileError::type_not_found(
                        ident.span,
                        name
                    ));

                    IndirectTyId::ERROR
                };

                (ident.span, id)
            }
            ast::Type::Array(array) => {
                array.with_inner(|inner| {
                    let span = inner.span();
                    let (inner, _, expr) = &inner.0;
                    let inner = self.resolve_ty(inner);
                    let len = self.resolve_anynonmous_const_expr(
                        expr,
                        IndirectTyId::USIZE,
                    );

                    (span, self.builder.types.mk_array(inner, len.eval_id))
                })
            },
            ast::Type::List(list) => {
                list.with_inner(|inner| {
                    let span = inner.span();
                    let elem = self.resolve_ty(&inner.0);
                    (span, self.builder.types.mk_list(elem))
                })
            }
            ast::Type::Fn(fn_ty) => {
                fn_ty.with_inner(|(kw_fn, args, ret)| {
                    let span_start = kw_fn.span();
                    let args_tys = args.0
                        .iter()
                        .map(|ty| self.resolve_ty(ty))
                        .collect();

                    let ret = match ret {
                        Some((_arrow, ret)) => self.resolve_ty_spanned(ret),
                        None => SpannedTy {
                            span: args.span(),
                            id: IndirectTyId::UNIT
                        },
                    };

                    (Span::merge(span_start, ret.span), self.builder.types.mk_fn(args_tys, ret.id))
                })
            },
        };

        SpannedTy {
            span,
            id: ty
        }
    }

    pub fn resolve_ty(&mut self, ty: &'ast ast::Type) -> IndirectTyId {
        self.resolve_ty_spanned(ty).id
    }

    pub fn resolve_expr(&mut self, expr: &'ast ast::Expr) -> ExprId {
        self.resolve_expr_spanned(expr).1
    }
}

impl<'ast, 'b> HirBuilder<'ast, 'b> {
    pub fn new(
        interner: &'b mut Interner,
        compile_errors: &'b mut Vec<CompileError>
    ) -> Self {
        Self {
            scopes: Arena::new(),
            definitions: Arena::new(),
            functions: Arena::new(),
            consts: Arena::new(),
            local_storages: Arena::new(),
            exprs: Arena::new(),
            blocks: Arena::new(),
            const_exprs: ConstantsEngine::new(),
            types: InferenceEngine::new(),
            analysis_stack: vec![],
            interner,
            compile_errors,
        }
    }

    fn queue_scope_items_inner(
        &mut self,
        id: GlobalScopeId,
        iter: &mut dyn Iterator<Item=&'ast Item>
    ) -> GlobalScopeId {
        let mut global_current_scope = GlobalScope::sub_scope(
            id,
            &mut self.scopes
        );

        for item in iter {
            let (def, name) = match item {
                Item::Function(func) => {
                    let name = func.signature.name;
                    let func = self.functions.store(None);
                    (Def::Function(func), name)
                },
                Item::Const(const_item) => {
                    let name = const_item.name;
                    let cnst = self.consts.store(None);
                    (Def::Const(cnst), name)
                },
            };

            let (def_id, slot) = self.definitions.reserve();
            slot.insert(def);
            self.analysis_stack.push((def_id, global_current_scope.id(), item));
            match global_current_scope.insert(name, def_id) {
                Ok(()) => {},
                Err(already_defined) => {
                    self.compile_errors.push(CompileError::duplicate_definition(
                        self.interner.resolve(name.symbol),
                        name.span,
                        already_defined
                    ))
                }
            }
        }


        global_current_scope.build()
    }


    fn queue_scope_items(
        &mut self,
        parent_id: GlobalScopeId,
        mut iter: impl Iterator<Item=&'ast Item>
    ) -> GlobalScopeId {
        self.queue_scope_items_inner(parent_id, &mut iter)
    }

    pub fn scope(
        &mut self,
        scope: GlobalScopeId,
        context: ParsingContext
    ) -> ScopedHirBuilder<'static, '_, 'ast, 'b> {
        ScopedHirBuilder {
            global_scope: scope,
            locals: BuilderLocalsData {
                context,
                state: LocalsState::Owned(LocalsDataStorage::Fresh),
            },
            builder: self
        }
    }
}

struct ImmutHir {
    scopes: Arena<GlobalScope>,
    definitions: Arena<Def>,
    local_storages: Arena<LocalStorage>,
    exprs: Arena<SpannedExpr>,
    blocks: Arena<Block>,
    functions: Arena<FuncDef>,
    consts: Arena<ConstDef>,
}

pub struct Hir {
    immut_hir: ImmutHir,
    type_engine: InferenceEngine,
    const_exprs: ConstantsEngine,
}

impl Hir {
    fn build(
        interner: &mut Interner,
        compile_errors: &mut Vec<CompileError>,
        module: &OvalModule,
    ) -> Self {
        let mut builder = HirBuilder::new(interner, compile_errors);
        builder.queue_scope_items(GlobalScopeId::ROOT, module.items.iter());
        while let Some((def_id, scope, item)) = builder.analysis_stack.pop() {
            let def = builder.definitions[def_id];
            match item {
                Item::Function(func_item) => {
                    let mut scope = builder.scope(scope, ParsingContext::Function);

                    let ast_args = func_item.signature.args.0.as_slice();

                    let (dup_args_count, duplicate_args) = {
                        let this = &mut *scope.builder;
                        let mut dup_args_cnt = 0;
                        let mut skip_args = None;
                        let mut names = HashMap::default();
                        for (i, &(_mut, arg_name, ..)) in ast_args.iter().enumerate() {
                            if let Err(err) = names.try_insert(arg_name.symbol, arg_name.span) {
                                this.compile_errors.push(CompileError::duplicate_definition(
                                    this.interner.resolve(arg_name.symbol),
                                    arg_name.span,
                                    *err.entry.get()
                                ));

                                let skip = skip_args.get_or_insert_with(|| {
                                    BitSet::new(ast_args.len())
                                });

                                skip.set(i);
                                dup_args_cnt += 1;
                            }
                        }

                        (dup_args_cnt, skip_args)
                    };

                    let mut args = Vec::with_capacity(ast_args.len() - dup_args_count);

                    let arg_tys = ast_args
                        .iter()
                        .enumerate()
                        .map(|(i, (mutable, arg_name, _colon, ty))| {
                            let ty = scope.resolve_ty_spanned(ty);
                            if duplicate_args.as_ref().is_none_or(|set| !set.get(i)) {
                                let arg_id = scope.insert_local(arg_name.symbol, LocalDef {
                                    name: arg_name.symbol,
                                    ty: Some(ty),
                                    mutable: mutable.is_some(),
                                });

                                args.push(arg_id)
                            }

                            ty.id
                        })
                        .collect();

                    let signature = func_item.signature.span();
                    let ret = match func_item.signature.ret {
                        Some((_arrow, ref ret)) => scope.resolve_ty_spanned(ret),
                        None => SpannedTy {
                            id: IndirectTyId::UNIT,
                            span: signature
                        }
                    };

                    let ty = scope.builder.types.mk_fn(arg_tys, ret.id);

                    let (body_span, block) = scope.resolve_block_spanned(&func_item.body);
                    let local_store = scope.locals.current_store();
                    let expr = builder.exprs.store(SpannedExpr {
                        span: body_span,
                        expr: Expr::Block(block),
                    });

                    let name = func_item.signature.name;
                    let function = FuncDef {
                        signature,
                        ret_ty_span: ret.span,
                        ty,
                        name,
                        args,
                        duplicate_args,
                        local_store,
                        is_const: func_item.signature.kw_const.is_some(),
                        body: expr,
                    };

                    let Def::Function(func_id) = def else {
                        unreachable!()
                    };
                    let slot = &mut builder.functions[func_id];
                    assert!(slot.is_none());
                    *slot = Some(function);
                }
                Item::Const(const_item) => {
                    let name = const_item.name;
                    let mut scope = builder.scope(scope, ParsingContext::Constant);
                    let ty = scope.resolve_ty_spanned(&const_item.ty);
                    let value = scope.resolve_declared_const_expr(
                        &const_item.assignment,
                        ty.id,
                        Span::merge(const_item.kw_const.span(), name.span),
                        ty.span
                    );

                    let Def::Const(cnst_id) = def else {
                        unreachable!()
                    };

                    let slot = &mut builder.consts[cnst_id];
                    assert!(slot.is_none());
                    *slot = Some(ConstDef {
                        name,
                        span: const_item.span(),
                        value: value.eval_id,
                    });
                }
            }
        }

        Self {
            immut_hir: ImmutHir {
                scopes: builder.scopes,
                definitions: builder.definitions,
                local_storages: builder.local_storages,
                exprs: builder.exprs,
                blocks: builder.blocks,
                functions: builder.functions.map_to(Option::unwrap),
                consts: builder.consts.map_to(Option::unwrap),
            },
            const_exprs: builder.const_exprs,
            type_engine: builder.types,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum BinClass {
    Arithmetic,
    Bitwise,
    Shift,
    Comparison,
    Equality,
    Logical,
}

fn classify_binop(op: BinOpKind) -> BinClass {
    match op {
        BinOpKind::Add
        | BinOpKind::Sub
        | BinOpKind::Mul
        | BinOpKind::Div
        | BinOpKind::Rem => BinClass::Arithmetic,

        BinOpKind::BitAnd | BinOpKind::BitOr | BinOpKind::BitXor => BinClass::Bitwise,

        BinOpKind::Shl | BinOpKind::Shr => BinClass::Shift,

        BinOpKind::Lt | BinOpKind::Le | BinOpKind::Gt | BinOpKind::Ge => BinClass::Comparison,

        BinOpKind::And | BinOpKind::Or => BinClass::Logical,

        BinOpKind::Eq | BinOpKind::Ne => BinClass::Equality,
    }
}

pub struct LocalDefTyMap(ArenaMap<LocalId, IndirectTyId>);

impl Storable for LocalDefTyMap {
    type Handle = LocalStoreId;
}

impl Deref for LocalDefTyMap {
    type Target = ArenaMap<LocalId, IndirectTyId>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for LocalDefTyMap {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}


struct LoopFrame {
    break_tys: Vec<SpannedTy>,
    break_exprs: Vec<ExprId>,
}

impl LoopFrame {
    pub fn new() -> Self {
        const {
            Self {
                break_tys: vec![],
                break_exprs: vec![]
            }
        }
    }

    pub fn push(&mut self, ty: SpannedTy, expr: ExprId) {
        self.break_tys.push(ty);
        self.break_exprs.push(expr);
    }
}

pub enum LValue {
    Local(LocalId),
    Index { container: ExprId, index: ExprId }
}

struct HirValidator<'hir, 'env> {
    interner: &'env mut Interner,
    errors: &'env mut Vec<CompileError>,

    hir: &'hir ImmutHir,
    const_exprs: ConstantsEngine,
    types: InferenceEngine,

    expr_ty: ArenaMap<ExprId, IndirectTyId>,
    lvalues: SparseArenaMapBuilder<ExprId, LValue>,
    coersions: SparseArenaMapBuilder<ExprId, Coersion>,
    local_types: Arena<LocalDefTyMap>,
}

macro_rules! get_ty_ctx {
    (@validator $this: expr) => {{
        TyCheckCtx {
            interner: $this.interner,
            errors: $this.errors,
            consts: &$this.const_exprs,
            funcs: &$this.hir.functions,
        }
    }};

    ($this: ident) => { get_ty_ctx!(@validator $this.validator) };
}

enum RetTy {
    Ret(SpannedTy),
    InvalidRet(SpannedTy),
}

struct ScopedHirValidator<'validator, 'hir, 'env> {
    locals: Option<LocalStoreId>,
    /// `None` means “not in a function” (so `return` is illegal).
    ret_ty: RetTy,
    loops: Vec<LoopFrame>,
    validator: &'validator mut HirValidator<'hir, 'env>
}

impl<'validator, 'hir, 'env> ScopedHirValidator<'validator, 'hir, 'env> {
    fn new(
        validator: &'validator mut HirValidator<'hir, 'env>,
        store: Option<LocalStoreId>,
        ret_ty: RetTy
    ) -> Self {
        Self {
            locals: store,
            ret_ty,
            loops: vec![],
            validator
        }
    }

    fn local_ty(&mut self, local: LocalId) -> IndirectTyId {
        let store = self.locals.unwrap();
        self.validator.local_types[store][local]
    }

    fn init_local(&mut self, local: LocalId, ty: IndirectTyId) {
        let store = self.locals.unwrap();
        self.validator.local_types[store].insert(local, ty);
    }

    fn infer_lvalue_type(&mut self, expr_id: ExprId) -> SpannedTy {
        let SpannedExpr { ref expr, span } = self.validator.hir.exprs[expr_id];

        let (lvalue, ty) = match *expr {
            Expr::Local(local) => {
                let store = self.locals.unwrap();
                let local_def = &self.validator.hir.local_storages[store][local];
                if !local_def.mutable {
                    self.validator.errors.push(CompileError::custom(
                        span,
                        format!(
                            "cannot assign twice to immutable variable `{}`",
                            self.validator.interner.resolve(local_def.name)
                        ),
                        "cannot assign twice to immutable variable"
                    ))
                }

                (Some(LValue::Local(local)), self.local_ty(local))
            },
            Expr::Index { container, index } => recurse(|| {
                let container_ty = self.infer_lvalue_type(container);
                let index_ty = self.infer_expr(index);
                let elem_ty = self.validator.types.index(
                    &mut get_ty_ctx!(self),
                    span,
                    container_ty,
                    index_ty
                );

                (Some(LValue::Index { container, index }), elem_ty)
            }),
            _ => {
                self.validator.errors.push(CompileError::custom(
                    span,
                    "invalid left-hand operand",
                    "cannot assign to this expression"
                ));
                (None, IndirectTyId::ERROR)
            }
        };

        if let Some(lvalue) = lvalue {
            self.validator.lvalues.insert(expr_id, lvalue);
        }

        SpannedTy {
            span,
            id: ty
        }
    }

    fn infer_expr(&mut self, expr_id: ExprId) -> SpannedTy {
        // FIXME coersion factoring
        let SpannedExpr { ref expr, span } = self.validator.hir.exprs[expr_id];

        let ty_id = match *expr {
            Expr::Error => IndirectTyId::ERROR,
            Expr::Literal(lit) => {
                self.validator.types.infer_literal(self.validator.errors, lit, span)
            },
            Expr::Local(local) => self.local_ty(local),
            Expr::Function(func) => self.validator.hir.functions[func].ty,
            Expr::Const(cnst) => {
                let eval_id = self.validator.hir.consts[cnst].value;
                self.validator.const_exprs[eval_id].ty
            },
            Expr::Assign { location, expr } => {
                recurse( || {
                    let location_ty = self.infer_lvalue_type(location);
                    let expr_ty = self.infer_expr(expr);
                    self.validator.types.assert_equal(
                        &mut get_ty_ctx!(self),
                        ConstraintSpan::with_constraint(expr_ty.span, location_ty.span),
                        location_ty.id,
                        expr_ty.id
                    );
                });
                IndirectTyId::UNIT
            }
            Expr::BinOp { lhs, op, rhs } => recurse(|| {
                let lhs_ty = self.infer_expr(lhs);
                let rhs_ty = self.infer_expr(rhs);
                let mut ctx = get_ty_ctx!(self);

                macro_rules! test_ty {
                    ($ty: expr; $pat: pat => $expr: expr) => {
                        match *self.validator.types.get_ty($ty) {
                            $pat => Some($expr),
                            _ => None
                        }
                    };
                }

                let lhs_as_list
                    = test_ty!(lhs_ty.id; InferTy::List(elem) => elem);
                let rhs_as_list
                    = test_ty!(rhs_ty.id; InferTy::List(elem) => elem);

                let loc = ConstraintSpan::new(span);
                match op {
                    BinOpKind::Add => {
                        match (lhs_as_list, rhs_as_list) {
                            (Some(elem1), Some(elem2)) => {
                                self.validator.types.assert_equal(
                                    &mut ctx,
                                    loc,
                                    elem1,
                                    elem2
                                );
                            },
                            (Some(_), None) | (None, Some(_)) => {
                                self.validator.types.assert_equal(
                                    &mut ctx,
                                    loc,
                                    rhs_ty.id,
                                    lhs_ty.id
                                );
                            }
                            (None, None) => {
                                // Only integer addition.
                                self.validator.types.assert_equal(
                                    &mut ctx,
                                    ConstraintSpan::new(span),
                                    lhs_ty.id,
                                    rhs_ty.id
                                );

                                let mut is_int = |ty: SpannedTy| {
                                    test_ty!(
                                        ty.id;
                                        InferTy::Infer(InferKind::Int, _)
                                        | InferTy::Primitive(PrimTy::Int(_)) => ()
                                    ).is_some()
                                };

                                if !is_int(lhs_ty) && !is_int(rhs_ty) {
                                    let int = self.validator.types.fresh_int_var(span);
                                    self.validator.types.assert_equal(&mut ctx, loc, lhs_ty.id, int);
                                }
                            }
                        }
                        lhs_ty.id
                    }

                    BinOpKind::Sub | BinOpKind::Mul | BinOpKind::Div | BinOpKind::Rem
                    | BinOpKind::BitAnd | BinOpKind::BitOr | BinOpKind::BitXor => {
                        self.validator.types.assert_equal(&mut ctx, loc, lhs_ty.id, rhs_ty.id);

                        let int = self.validator.types.fresh_int_var(span);
                        self.validator.types.assert_equal(&mut ctx, loc, lhs_ty.id, int);

                        int
                    }

                    BinOpKind::Shl | BinOpKind::Shr => {
                        let shifted_int = self.validator.types.fresh_int_var(span);
                        self.validator.types.assert_equal(&mut ctx, loc, lhs_ty.id, shifted_int);

                        let shifter_int = self.validator.types.fresh_int_var(span);
                        self.validator.types.assert_equal(&mut ctx, loc, rhs_ty.id, shifter_int);

                        shifted_int
                    }

                    // --- Ordering comparisons: (recommended) Int cmp Int, returns bool ---
                    BinOpKind::Lt | BinOpKind::Le | BinOpKind::Gt | BinOpKind::Ge => {
                        self.validator.types.assert_equal(&mut ctx, loc, lhs_ty.id, rhs_ty.id);

                        let int = self.validator.types.fresh_int_var(span);
                        self.validator.types.assert_equal(&mut ctx, loc, lhs_ty.id, int);

                        IndirectTyId::BOOL
                    }

                    // --- Equality: keep your existing "same type" rule ---
                    BinOpKind::Eq | BinOpKind::Ne => {
                        self.validator.types.assert_equal(&mut ctx, loc, lhs_ty.id, rhs_ty.id);
                        IndirectTyId::BOOL
                    }

                    // --- Logical: bool op bool ---
                    BinOpKind::And | BinOpKind::Or => {
                        self.validator.types.assert_equal(
                            &mut ctx,
                            ConstraintSpan::new(lhs_ty.span),
                            IndirectTyId::BOOL,
                            lhs_ty.id
                        );

                        self.validator.types.assert_equal(
                            &mut ctx,
                            ConstraintSpan::new(rhs_ty.span),
                            IndirectTyId::BOOL,
                            rhs_ty.id
                        );

                        IndirectTyId::BOOL
                    }
                }
            }),
            Expr::UnOp { op, expr } => recurse(|| {
                // currently all unops take T -> T
                let _ = op;
                self.infer_expr(expr).id
            }),
            Expr::CastAs { expr, to } => recurse(|| {
                let from_ty = self.infer_expr(expr);
                self.validator.types.assert_casts(
                    &mut get_ty_ctx!(self),
                    ConstraintSpan::with_constraint(from_ty.span, to.span),
                    from_ty,
                    to
                );
                to.id
            }),
            Expr::Call { callee, ref args } => recurse(|| {
                let callee_ty = self.infer_expr(callee);
                let args_ty = args
                    .iter()
                    .map(|&expr| self.infer_expr(expr))
                    .collect();

                let (coersions, ret) = self.validator.types.call_fn(
                    &mut get_ty_ctx!(self),
                    span,
                    callee_ty,
                    args_ty
                );

                for (i, coersion) in coersions {
                    self.validator.coersions.insert(args[i], coersion)
                }

                ret
            }),
            Expr::Index { container, index } => recurse(|| {
                let container = self.infer_expr(container);
                let index = self.infer_expr(index);
                self.validator.types.index(
                    &mut get_ty_ctx!(self),
                    span,
                    container,
                    index
                )
            }),

            Expr::Tuple(ref exprs) if exprs.is_empty() => IndirectTyId::UNIT,
            Expr::Tuple(ref exprs) => recurse(|| {
                let tys = exprs
                    .iter()
                    .map(|&expr| self.infer_expr(expr).id)
                    .collect();

                self.validator.types.mk_tuple(tys)
            }),

            Expr::ArraySplat { element, len } => recurse(|| {
                let elem = self.infer_expr(element).id;
                self.validator.types.mk_array(elem, len.eval_id)
            }),
            Expr::Array(ref exprs) => recurse(|| {
                let len = exprs.len();
                let len = self.validator.const_exprs.add_length(span, len);

                let tys = exprs
                    .iter()
                    .map(|&expr| self.infer_expr(expr))
                    .collect::<Vec<_>>();

                let (coersions, elem) = self.validator.types.coerce_all(
                    &mut get_ty_ctx!(self),
                    span,
                    &tys
                );

                for (i, coersion) in coersions {
                    self.validator.coersions.insert(exprs[i], coersion)
                }

                self.validator.types.mk_array(elem, len)
            }),
            Expr::Return(inner_expr) => {
                let ret_ty = match self.ret_ty {
                    RetTy::Ret(ty) => ty,
                    RetTy::InvalidRet(ty) => ty,
                };

                if !matches!(self.ret_ty, RetTy::Ret(_)) {
                    self.validator.errors.push(CompileError::custom(
                        span,
                        "return statement outside of function body",
                        "here"
                    ))
                }

                let inner_ty = recurse(|| self.infer_expr(inner_expr));

                let coersion = self.validator.types.coerce_spanned(
                    &mut get_ty_ctx!(self),
                    inner_ty,
                    ret_ty
                );

                if let Some(coersion) = coersion {
                    self.validator.coersions.insert(inner_expr, coersion)
                }

                IndirectTyId::NEVER
            }
            Expr::Break(inner) => {
                match self.loops.len().checked_sub(1) {
                    None => self.validator.errors.push(CompileError::custom(
                        span,
                        "`break` outside of a loop",
                        "cannot `break` outside of a loop"
                    )),
                    Some(i) => {
                        let inner_ty = recurse(|| self.infer_expr(inner));
                        self.loops[i].push(inner_ty, inner)
                    }
                }

                IndirectTyId::NEVER
            },
            Expr::Continue => {
                if self.loops.is_empty() {
                    self.validator.errors.push(CompileError::custom(
                        span,
                        "`continue` outside of a loop",
                        "cannot `continue` outside of a loop"
                    ))
                }
                IndirectTyId::NEVER
            },
            Expr::Block(block) => {
                let ret = recurse(|| self.infer_block(block).0);
                self.validator.expr_ty.insert(expr_id, ret.id);
                return ret
            },
            Expr::Loop(block) => recurse(|| {
                self.loops.push(LoopFrame::new());

                let (loop_ret, _) = self.infer_block(block);
                self.validator.types.assert_equal(
                    &mut get_ty_ctx!(self),
                    ConstraintSpan::new(loop_ret.span),
                    IndirectTyId::UNIT,
                    loop_ret.id
                );

                let Some(LoopFrame { break_tys, break_exprs }) = self.loops.pop() else {
                    unreachable!()
                };

                match break_tys.as_slice() {
                    [] => IndirectTyId::NEVER,
                    many => {
                        let (coersions, ret) = self.validator.types.coerce_all(
                            &mut get_ty_ctx!(self),
                            span,
                            many
                        );

                        for (i, coersion) in coersions {
                            self.validator.coersions.insert(break_exprs[i], coersion)
                        }

                        ret
                    }
                }
            }),
            Expr::If {
                if_so,
                ref else_if,
                else_branch
            } => recurse(|| {
                let mut tys = vec![];
                let mut exprs = vec![];

                let mut process_no_else = |this: &mut Self, body: BlockId| {
                    let (body_ty, _final_expr) = this.infer_block(body);
                    this.validator.types.assert_equal(
                        &mut get_ty_ctx!(this),
                        ConstraintSpan::new(body_ty.span),
                        IndirectTyId::UNIT,
                        body_ty.id
                    );
                };
                let mut process_with_else = |this: &mut Self, body: BlockId| {
                    let (body_ty, final_expr) = this.infer_block(body);
                    tys.push(body_ty);
                    exprs.push(final_expr)
                };
                let process_body = match else_branch {
                    None => (&mut process_no_else) as &mut dyn FnMut(&mut Self, BlockId),
                    Some(_) => &mut process_with_else,
                };

                let mut process = |this: &mut Self, branch: IfBranch| {
                    let ty = this.infer_expr(branch.condition);
                    this.validator.types.assert_equal(
                        &mut get_ty_ctx!(this),
                        ConstraintSpan::new(ty.span),
                        IndirectTyId::BOOL,
                        ty.id
                    );
                    process_body(this, branch.body)
                };

                process(self, if_so);
                for &else_if in else_if {
                    process(self, else_if);
                }

                match else_branch {
                    Some(else_branch) => {
                        process_with_else(self, else_branch);
                        let (coersions, ty) = self.validator.types.coerce_all(
                            &mut get_ty_ctx!(self),
                            span,
                            &tys,
                        );

                        for (i, coersion) in coersions {
                            self.validator.coersions.insert(exprs[i], coersion);
                        }

                        ty
                    },
                    None => IndirectTyId::UNIT
                }
            })
        };

        self.validator.expr_ty.insert(expr_id, ty_id);
        SpannedTy {
            span,
            id: ty_id
        }
    }

    fn infer_block(&mut self, block_id: BlockId) -> (SpannedTy, ExprId) {
        let Block { ref stmts, trailing_expr } = self.validator.hir.blocks[block_id];

        let mut last_stmt_never = None;
        for stmt in stmts {
            last_stmt_never = match *stmt {
                Stmt::Expression { expr, is_expr_stmt } => {
                    let ty = self.infer_expr(expr);
                    if is_expr_stmt {
                        let coersion = self.validator.types.coerce(
                            &mut get_ty_ctx!(self),
                            ConstraintSpan::new(ty.span),
                            IndirectTyId::UNIT,
                            ty.id
                        );

                        if let Some(coersion) = coersion {
                            self.validator.coersions.insert(expr, coersion)
                        }
                    }

                    self.validator.types.is_never(ty.id).then_some((ty, expr))
                }
                Stmt::Let { local, initializer, span } => {
                    let store = self.locals.unwrap();
                    let local_ty = self.validator.hir.local_storages[store][local].ty;
                    let ty = match (local_ty, initializer) {
                        (None, None) => self.validator.types.fresh_var(span),
                        (Some(ty), None) => ty.id,
                        (None, Some(expr)) => self.infer_expr(expr).id,
                        (Some(ty), Some(expr_id)) => {
                            let expr = self.infer_expr(expr_id);
                            let coersion = self.validator.types.coerce_spanned(
                                &mut get_ty_ctx!(self),
                                expr,
                                ty
                            );

                            if let Some(coersion) = coersion {
                                self.validator.coersions.insert(expr_id, coersion)
                            }

                            ty.id
                        }
                    };
                    self.init_local(local, ty);
                    None
                }
            }
        }

        match (trailing_expr, last_stmt_never) {
            (TrailingExpr::Trailing(expr), _) => (self.infer_expr(expr), expr),
            (TrailingExpr::FallbackUnit(_), Some(last_stmt)) => last_stmt,
            (TrailingExpr::FallbackUnit(expr), None) => {
                let span = self.validator.hir.exprs[expr].span;
                let ty = SpannedTy {
                    span,
                    id: IndirectTyId::UNIT,
                };
                (ty, expr)
            }
        }
    }
}

pub struct TypedHir {
    pub local_storages: Arena<LocalStorage>,
    pub exprs: Arena<SpannedExpr>,
    pub blocks: Arena<Block>,
    pub const_exprs: ConstantsEngine,
    pub functions: Arena<FuncDef>,
    pub consts: Arena<ConstDef>,
    pub expr_ty: ArenaMap<ExprId, IndirectTyId>,
    pub lvalues: SparseArenaMap<ExprId, LValue>,
    pub coersions: SparseArenaMap<ExprId, Coersion>,
    pub local_types: Arena<LocalDefTyMap>,
    pub types: ResolvedTypes,
}

impl TypedHir {
    fn build(
        interner: &mut Interner,
        compile_errors: &mut Vec<CompileError>,
        hir: Hir,
    ) -> Result<Self, ()> {
        let mut validator = HirValidator {
            interner,
            errors: compile_errors,
            hir: &hir.immut_hir,
            const_exprs: hir.const_exprs,
            types: hir.type_engine,
            expr_ty: hir.immut_hir.exprs.make_side_table(),
            lvalues: hir.immut_hir.exprs.sparse_table_builder(),
            coersions: hir.immut_hir.exprs.sparse_table_builder(),
            local_types: hir.immut_hir.local_storages.map_cloned(|local_store| {
                LocalDefTyMap(local_store.make_side_table())
            }),
        };

        for (_def_id, def) in validator.hir.definitions.iter() {
            match *def {
                Def::Const(_) => {/* type checked at const_exprs */},
                Def::Function(func) => {
                    let func = &validator.hir.functions[func];
                    let &InferTy::Fn(_, ret) = validator.types.get_ty(func.ty) else {
                        unreachable!()
                    };

                    let ret = SpannedTy { id: ret, span: func.ret_ty_span };

                    let mut scoped_validator = ScopedHirValidator::new(
                        &mut validator,
                        func.local_store,
                        RetTy::Ret(ret)
                    );

                    for &arg in &func.args {
                        let store = func.local_store.unwrap();
                        let ty = scoped_validator.validator.hir.local_storages[store][arg]
                            .ty
                            .unwrap();

                        scoped_validator.init_local(arg, ty.id)
                    }

                    let ty = scoped_validator.infer_expr(func.body);

                    let coersion = scoped_validator.validator.types.coerce_spanned(
                        &mut get_ty_ctx!(scoped_validator),
                        ty,
                        ret,
                    );

                    if let Some(coersion) = coersion {
                        scoped_validator.validator.coersions.insert(func.body, coersion);
                    }
                }
            }
        }

        for expr_id in validator.const_exprs.keys() {
            let expr = &validator.const_exprs[expr_id];
            match expr.expr {
                ConstExpr::ArrayLen(_atom, _expr_span) => {
                    // atoms are made pre type checked
                }
                ConstExpr::LateInit {
                    locals,
                    expr: inner_expr,
                } => {
                    let expected = expr.ty;
                    let ty_span = expr.ty_span;
                    let expected = SpannedTy { id: expected, span: ty_span };

                    let mut scope = ScopedHirValidator::new(
                        &mut validator,
                        locals,
                        RetTy::InvalidRet(expected)
                    );

                    let ty = scope.infer_expr(inner_expr);
                    let coersion = validator.types.coerce_spanned(
                        &mut get_ty_ctx!(@validator validator),
                        ty,
                        expected
                    );

                    if let Some(coersion) = coersion {
                        validator.coersions.insert(inner_expr, coersion)
                    }
                }
            };
        }

        let types = validator
            .types
            .solve(&mut get_ty_ctx!(@validator validator));

        let HirValidator {
            interner: _,
            errors: _,
            hir: _,
            const_exprs,
            types: _,
            expr_ty,
            lvalues,
            coersions,
            local_types
        } = validator;

        let ImmutHir {
            scopes: _,
            definitions: _,
            local_storages,
            exprs,
            blocks,
            functions,
            consts
        } = hir.immut_hir;

        if !compile_errors.is_empty() {
            return Err(())
        }

        Ok(TypedHir {
            local_storages,
            exprs,
            blocks,
            const_exprs,
            functions,
            consts,
            expr_ty,
            lvalues: lvalues.build(),
            coersions: coersions.build(),
            local_types,
            types: types?,
        })
    }
}

pub fn make_hir(
    interner: &mut Interner,
    compile_errors: &mut Vec<CompileError>,
    module: OvalModule,
) -> Hir {
    let hir = Hir::build(
        interner,
        compile_errors,
        &module
    );

    // drop module to save memory
    drop(module);

    hir
}

pub fn type_check_hir(
    interner: &mut Interner,
    compile_errors: &mut Vec<CompileError>,
    hir: Hir,
) -> Result<TypedHir, ()> {
    TypedHir::build(interner, compile_errors, hir)
}