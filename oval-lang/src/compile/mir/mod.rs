use crate::alloc_helper::{make_slice, slice};
use crate::arena::{from_raw_handle, make_handle, make_handle_raw, to_raw_handle, Arena, ArenaMap, EmptyConstructable, FilledArenaMap, HandleInt, HandleRaw, Storable};
use crate::ast::UnOpKind;
use crate::compile::algorithms::{dfs_cyclic, Cycle};
use crate::compile::hir::{Block, BlockId, ConstConstraintId, ConstEvalId, ConstExpr, ConstExprFull, ConstantsEngine, Expr, ExprId, FuncDef, FuncId, LValue, LiteralValue, LocalStoreId, PrimTy, SpannedExpr, SpannedTy, Stmt, TrailingExpr, TypedHir};
use crate::compile::mir::scalar::{ParseIntLiteralError, Scalar};
use crate::compile::{algorithms, hir, CompileError};
use crate::hashed::{HashMap, HashSet};
use crate::interner::Interner;
use crate::spanned::Span;
use crate::{alloc_helper, recurse};
use alloc::boxed::Box;
use alloc::vec::Vec;
use alloc::{format, vec};
use cfg_if::cfg_if;
use core::iter;

pub(crate) mod scalar;

const fn int_discriminant(bit_count: u8, is_signed: bool) -> u8 {
    assert!(bit_count <= 64 && bit_count >= 1);
    (64 - bit_count) | ((is_signed as u8) * 128)
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
#[repr(u8)]
pub enum IntTy {
    U64 = int_discriminant(64, false),
    U32 = int_discriminant(32, false),
    U16 = int_discriminant(16, false),
    U8 = int_discriminant(8, false),

    I64 = int_discriminant(64, true),
    I32 = int_discriminant(32, true),
    I16 = int_discriminant(16, true),
    I8 = int_discriminant(8, true)
}

impl IntTy {
    cfg_if! {
        if #[cfg(target_pointer_width = "64")] {
            pub const USIZE: Self = Self::U64;
            pub const ISIZE: Self = Self::I64;
        } else if #[cfg(target_pointer_width = "32")] {
            pub const USIZE: Self = Self::U32;
            pub const ISIZE: Self = Self::I32;
        } else if #[cfg(target_pointer_width = "16")] {
            pub const USIZE: Self = Self::U16;
            pub const ISIZE: Self = Self::I16;
        } else {
            compile_error!("unsupported target")
        }
    }

    #[inline(always)]
    const fn inverse_bits(self) -> u8 {
        (self as u8) & !128
    }
    
    #[inline(always)]
    pub const fn is_signed(self) -> bool {
        ((self as u8) & 128) != 0
    }

    #[inline(always)]
    const fn select(self, unsigned: u64, signed: i64) -> u64 {
        // Turn bool into 0 / !0
        let sign_mask = (self.is_signed() as u64).wrapping_neg();
        (signed.cast_unsigned() & sign_mask) | (unsigned & !sign_mask)
    }

    #[inline(always)]
    pub const fn select_bool(self, is_unsigned: bool, is_signed: bool) -> bool {
        let sign = self.is_signed();
        (is_signed & sign) | (is_unsigned & !sign)
    }

    #[inline(always)]
    pub const fn mask(self, int: u64) -> u64 {
        let inv_bits = self.inverse_bits() as u32;
        // integer is now truncated and shifted into position of the sign bit
        // SAFETY: inv_bits = 64 - bit_count, bit_count ∈ [1, 64], so inv_bits ∈ [0, 63].
        let trunc = unsafe { int.unchecked_shl(inv_bits) };

        let unsigned = unsafe { trunc.unchecked_shr(inv_bits) };
        let signed = unsafe { trunc.cast_signed().unchecked_shr(inv_bits) };
        self.select(unsigned, signed)
    }

    #[inline(always)]
    pub const fn select_masked(self, int: u64, signed: i64) -> u64 {
        let inv_bits = self.inverse_bits() as u32;
        // truncate and place in proper sign bit, the sign extend according to type
        // SAFETY: inv_bits = 64 - bit_count, bit_count ∈ [1, 64], so inv_bits ∈ [0, 63].
        let unsigned = unsafe { int.unchecked_shl(inv_bits).unchecked_shr(inv_bits) };
        let signed = unsafe { signed.unchecked_shl(inv_bits).unchecked_shr(inv_bits) };
        self.select(unsigned, signed)
    }
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub enum Ty {
    Int(IntTy),
    Tuple(Box<[TyId]>),
    List(TyId),
    Array { 
        elem: TyId,
        len: usize,
    },
    Fn(Box<[TyId]>, TyId),
}

make_handle! {
    pub TyId for Ty: Sized;
    internable;
    with constants {
        pub U64 = Ty::Int(IntTy::U64);
        pub U32 = Ty::Int(IntTy::U32);
        pub U16 = Ty::Int(IntTy::U16);
        pub U8 = Ty::Int(IntTy::U8);

        pub I64 = Ty::Int(IntTy::I64);
        pub I32 = Ty::Int(IntTy::I32);
        pub I16 = Ty::Int(IntTy::I16);
        pub I8 = Ty::Int(IntTy::I8);

        pub UNIT = Ty::Tuple(alloc_helper::empty_slice());
    }
}

#[derive(Debug)]
pub enum MirDef {
    Func(FuncId),
    Const(ConstEvalId),
    Constraint(ConstConstraintId)
}

make_handle_raw!(pub MirDefId);

impl Storable for MirDef {
    type Handle = MirDefId;
}

pub struct MirOrderBuilder<'a, 'env> {
    order: MirOrderer<'a>,
    errors: &'env mut Vec<CompileError>,
    interner: &'env mut Interner,
    deps: ArenaMap<MirDefId, HashMap<MirDefId, Span>>,
}

impl<'a, 'env> MirOrderBuilder<'a, 'env> {
    pub fn with_scope<T>(
        &mut self,
        const_ctx: bool,
        def_id: impl FnOnce(&MirOrderer) -> MirDefId,
        func: impl FnOnce(&mut ScopedMirOrderBuilder<'_, 'a, 'env>) -> T
    ) -> T {
        let def_id = def_id(&self.order);
        let mut scope = ScopedMirOrderBuilder {
            builder: self,
            depends_on: HashMap::default(),
            is_const: const_ctx
        };
        let ret = func(&mut scope);
        let depends_on = scope.depends_on;
        self.deps.insert(def_id, depends_on);
        ret
    }
}

pub struct ScopedMirOrderBuilder<'b, 'a, 'env> {
    builder: &'b mut MirOrderBuilder<'a, 'env>,
    depends_on: HashMap<MirDefId, Span>,
    is_const: bool
}

impl<'b, 'a, 'err> ScopedMirOrderBuilder<'b, 'a, 'err> {
    fn add_dep(&mut self, def_id: MirDefId, span: Span) {
        // try_insert so that the first usage span actually shows up and not the last
        let _ = self.depends_on.try_insert(def_id, span);
    }

    fn add_cnst_dep(&mut self, cnst: ConstEvalId, span: Span) {
        let def_id = self.builder.order.cnst_to_def(cnst);
        self.add_dep(def_id, span)
    }

    fn add_func_dep(&mut self, cnst: FuncId, span: Span) {
        let def_id = self.builder.order.fn_to_def(cnst);
        self.add_dep(def_id, span)
    }

    fn add_ty_deps_inner(&mut self, ty: hir::TyId, span: Span) {
        let ir = self.builder.order.ir;
        let mut loop_ty = ty;
        loop {
            let ty = loop_ty;
            loop_ty = match ir.types.types[ty] {
                hir::Ty::Primitive(_) => return,
                hir::Ty::List(elem) => elem,
                hir::Ty::Array(elem, len) => {
                    self.add_cnst_dep(len, span);
                    elem
                }
                hir::Ty::Tuple(ref tys) => match **tys {
                    [] => return,
                    [one] => {
                        one
                    },
                    [ref rest @ .., last] => {
                        recurse(|| for &ty in rest {
                            self.add_ty_deps_inner(ty, span)
                        });
                        last
                    }
                }
                hir::Ty::Fn(ref args, ret) => {
                    if !args.is_empty() {
                        recurse(|| for &arg in args.iter() {
                            self.add_ty_deps_inner(arg, span)
                        })
                    }
                    ret
                },
            }
        }
    }

    fn add_ty_deps(&mut self, ty: SpannedTy) {
        let ty_id = self.builder.order.ir.types.resolve(ty.id);
        self.add_ty_deps_inner(ty_id, ty.span)
    }

    fn add_expr_deps(&mut self, expr_id: ExprId) {
        let ir = self.builder.order.ir;
        let is_const = self.is_const;

        let mut loop_expr = expr_id;
        loop {
            let expr_id = loop_expr;
            let SpannedExpr { ref expr, span } = ir.exprs[expr_id];
            self.add_ty_deps(SpannedTy {
                span,
                id: ir.expr_ty[expr_id]
            });

            let add_block_deps = |this: &mut Self, block: BlockId| {
                let Block { ref stmts, trailing_expr } = ir.blocks[block];
                let iter_trailing = match trailing_expr {
                    TrailingExpr::Trailing(expr) => Some(expr),
                    TrailingExpr::FallbackUnit(_) => None
                };
                let iter = stmts
                    .iter()
                    .filter_map(|stmt| match *stmt {
                        Stmt::Expression { expr, is_expr_stmt: _ } => Some(expr),
                        // dependencies of the type hints of locals
                        // are added from local storage pass
                        Stmt::Let {
                            local: _,
                            initializer,
                            span: _,
                        } => initializer,
                    })
                    .chain(iter_trailing);

                for expr in iter {
                    this.add_expr_deps(expr)
                }
            };

            let _process_many = |this: &mut Self, elements: &[ExprId]| {
                match *elements {
                    [] => None,
                    [one] => Some(one),
                    [ref rest @ .., last] => {
                        recurse(|| for &expr in rest {
                            this.add_expr_deps(expr);
                        });
                        Some(last)
                    }
                }
            };

            macro_rules! process_many {
                ($elements:expr) => {
                    match _process_many(self, $elements) {
                        Some(expr) => expr,
                        None => return,
                    }
                };
            }

            loop_expr = match *expr {
                Expr::Error
                | Expr::Function(_)
                | Expr::Continue
                | Expr::Local(_)
                | Expr::Literal(_) => return,

                Expr::Assign { location: _, expr } => {
                    // currently no lvalue can ever depend on a constant of function
                    fn _assert(lvalue: LValue) {
                        match lvalue {
                            LValue::Local(_) => {}
                            LValue::Index { .. } => {}
                        }
                    }

                    expr
                }

                Expr::Const(id) => {
                    let const_def = &ir.consts[id];
                    self.add_cnst_dep(const_def.value, span);
                    return;
                },

                Expr::CastAs { expr, to } => {
                    self.add_ty_deps(to);
                    expr
                }
                Expr::Call { callee, ref args } => {
                    // the dependency spans the whole call site
                    let SpannedExpr { expr: ref callee_expr, span: _ } = ir.exprs[callee];
                    match *callee_expr {
                        Expr::Function(func_id)
                            // if this isn't in a const context
                            // its always fine to add the dependency
                            if ir.functions[func_id].is_const || !is_const
                        => {
                            self.add_func_dep(func_id, span)
                        },
                        Expr::Function(func_id) => {
                            let name = ir.functions[func_id].name.symbol;
                            self.builder.errors.push(CompileError::custom(
                                span,
                                format!(
                                    "cannot call non-const function `{}` in constants",
                                    self.builder.interner.resolve(name)
                                ),
                                "call here"
                            ))
                        }
                        _ => match is_const {
                            true => self.builder.errors.push(CompileError::custom(
                                span,
                                "function pointer calls are not allowed in constants",
                                "call here"
                            )),
                            false => recurse(|| self.add_expr_deps(callee)),
                        },
                    }

                    process_many!(args)
                },

                Expr::Index { container: one, index: two }
                | Expr::BinOp { lhs: one, op: _, rhs: two } => {
                    recurse(|| self.add_expr_deps(one));
                    two
                }

                Expr::Return(expr)
                | Expr::Break(expr)
                | Expr::UnOp { op: _, expr } => expr,

                Expr::Array(ref elements)
                | Expr::Tuple(ref elements) => process_many!(elements),
                Expr::ArraySplat { element, len } => {
                    self.add_cnst_dep(len.eval_id, len.span);
                    element
                }
                Expr::Block(block)
                | Expr::Loop(block) => {
                    recurse(|| add_block_deps(self, block));
                    return;
                },
                Expr::If {
                    if_so,
                    ref else_if,
                    else_branch
                } => {
                    recurse(|| {
                        let iter = iter::once(if_so)
                            .chain(else_if.iter().copied())
                            .map(|br| br.body)
                            .chain(else_branch);

                        for block in iter {
                            add_block_deps(self, block)
                        }
                    });
                    return;
                }
            };
        }
    }

    fn add_local_store_deps(&mut self, store: Option<LocalStoreId>) {
        let Some(store) = store else {
            return;
        };

        let ir = self.builder.order.ir;
        let store = &ir.local_storages[store];
        for (_id, local_def) in store.iter() {
            if let Some(ty) = local_def.ty {
                self.add_ty_deps(ty)
            }
        }
    }
}

pub struct MirOrderer<'a> {
    ir: &'a TypedHir,
    constrait_offset: HandleInt,
    len: HandleInt,
}

impl<'a> MirOrderer<'a> {
    pub fn new(ir: &'a TypedHir) -> Self {
        #[cold]
        #[inline(never)]
        fn too_many_items<T>() -> T {
            panic!("too many items")
        }

        let (constrait_offset, len_items) = ir
            .const_exprs
            .count()
            .checked_add(ir.functions.count())
            .and_then(|offset| {
                Some((offset, offset.checked_add(ir.types.equal_constants.count())?))
            })
            .unwrap_or_else(too_many_items);

        if len_items > 0 {
            let max_id = HandleRaw::handle_count_to_usize(len_items - 1);
            if MirDefId::new(max_id).is_none() {
                too_many_items()
            }
        }

        Self {
            ir,
            constrait_offset,
            len: len_items
        }
    }

    pub fn cnst_to_def(&self, id: ConstEvalId) -> MirDefId {
        assert!(id.get() < self.ir.const_exprs.len());
        from_raw_handle(to_raw_handle(id))
    }

    pub fn fn_to_def(&self, id: FuncId) -> MirDefId {
        let id_raw = id.as_handle_count();
        assert!(id_raw < self.ir.functions.count());
        let id = unsafe {
            let idx = id_raw.unchecked_add(self.ir.const_exprs.count());
            HandleRaw::from_handle_int(idx).unwrap_unchecked()
        };
        from_raw_handle(id)
    }

    pub fn const_constraint_to_def(&self, id: ConstConstraintId) -> MirDefId {
        let id_raw = id.as_handle_count();
        assert!(id_raw < self.ir.types.equal_constants.count());
        let id = unsafe {
            let idx = id_raw.unchecked_add(self.constrait_offset);
            HandleRaw::from_handle_int(idx).unwrap_unchecked()
        };
        from_raw_handle(id)
    }

    pub fn get_mir_def(&self, id: MirDefId) -> MirDef {
        assert!(id.as_handle_count() < self.len);

        let raw = to_raw_handle(id);
        let idx = raw.as_handle_int();
        let cutoff = self.ir.const_exprs.count();
        match idx < cutoff {
            true => MirDef::Const(from_raw_handle(raw)),
            false if idx < self.constrait_offset => {
                let id_raw = unsafe {
                    // Safety: id_raw >= cutoff
                    // doing this avoids marking this branch cold
                    // since `checked_sub` assumes the fail case is cold
                    let id = idx.unchecked_sub(cutoff);
                    // Safety: this id is <= the original id
                    // and that means this ID must be valid
                    HandleRaw::from_handle_int(id).unwrap_unchecked()
                };
                MirDef::Func(from_raw_handle(id_raw))
            },
            false => {
                let id_raw = unsafe {
                    // Safety: id_raw >= self.constrait_offset
                    // since we are in the fallback branch
                    // doing this avoids marking this branch cold
                    // since `checked_sub` assumes the fail case is cold
                    let id = idx.unchecked_sub(self.constrait_offset);
                    // Safety: this id is <= the original id
                    // and that means this ID must be valid
                    HandleRaw::from_handle_int(id).unwrap_unchecked()
                };
                MirDef::Constraint(from_raw_handle(id_raw))
            }
        }
    }

    fn compute_order(
        &self,
        errors: &mut Vec<CompileError>,
        interner: &mut Interner,
    ) -> (Vec<MirDefId>, Vec<Cycle<Span>>) {
        let total_items = HandleRaw::handle_count_to_usize(self.len);

        let mut mir_order_builder = MirOrderBuilder {
            order: MirOrderer { ..*self },
            errors,
            interner,
            deps: ArenaMap::new_with_length(total_items),
        };

        for (function_id, function_def) in mir_order_builder.order.ir.functions.iter() {
            let FuncDef {
                signature,
                ty,
                ret_ty_span: _,
                name: _,
                args: _,
                duplicate_args: _,
                local_store,
                is_const,
                body,
            } = *function_def;

            mir_order_builder.with_scope(
                is_const,
                |order| order.fn_to_def(function_id),
                |scope| {
                    scope.add_ty_deps(SpannedTy { span: signature, id: ty });
                    scope.add_local_store_deps(local_store);
                    scope.add_expr_deps(body);
                },
            );
        }

        for (const_eval_id, const_expr_full) in mir_order_builder.order.ir.const_exprs.iter() {
            let ConstExprFull {
                decl_span: _,
                ty,
                ty_span,
                ref expr
            } = *const_expr_full;

            mir_order_builder.with_scope(
                /* is_const */ true,
                |order| order.cnst_to_def(const_eval_id),
                |scope| {
                    scope.add_ty_deps(SpannedTy { span: ty_span, id: ty });
                    match *expr {
                        ConstExpr::ArrayLen(..) => {}
                        ConstExpr::LateInit { locals, expr } => {
                            scope.add_local_store_deps(locals);
                            scope.add_expr_deps(expr);
                        }
                    }
                },
            );
        }

        for (constraint_id, &constraint, _span) in mir_order_builder.order.ir.types.equal_constants.iter() {
            let def_id = mir_order_builder.order.const_constraint_to_def(constraint_id);
            let deps = constraint.ids_equal().into_iter().map(|id| {
                (
                    mir_order_builder.order.cnst_to_def(id),
                    // constraints never produce a cycle since nothing depends on them
                    Span::new(usize::MAX, usize::MAX)
                )
            });
            mir_order_builder.deps.insert(def_id, deps.collect());
        }

        let MirOrderBuilder {
            order: _,
            errors: _,
            interner: _,
            deps
        } = mir_order_builder;

        let forward_edges = deps.fill_with(|_| HashMap::default());

        let reverse_edges: Box<[Vec<MirDefId>]> = {
            let mut rev = make_slice(|_| vec![], total_items);
            for (definition_id, deps) in forward_edges.iter() {
                for (&dependency_id, _) in deps {
                    rev[dependency_id.get()].push(definition_id);
                }
            }
            rev
        };

        // ---- Kosaraju SCC ----
        let finish_order: Vec<MirDefId> = dfs_cyclic(
            Vec::with_capacity(total_items),
            forward_edges.keys(),
            |stack, _ord, def_id| {
                stack.push(forward_edges[def_id].iter().map(|(&child, _)| child))
            },
            |ord, done| ord.push(done),
            total_items
        );

        struct Scc(Vec<MirDefId>);

        make_handle_raw!(SccId);

        impl Storable for Scc { type Handle = SccId; }
        impl EmptyConstructable for Scc {}


        let (scc_id_for_def, scc_graph) = {
            let scc_id_for_definition: ArenaMap<MirDefId, SccId> =
                ArenaMap::new_with_length(total_items);
            let mut strongly_connected_components: Arena<Scc> =
                Arena::with_capacity(total_items);

            let active_depth: usize = 0;

            let (first_id, _slot) = strongly_connected_components.reserve();
            let current_scc_id = first_id;
            let current_component: Vec<MirDefId> = vec![];

            let (scc_ids, sccs, ..) = dfs_cyclic(
                (
                    scc_id_for_definition,
                    strongly_connected_components,
                    active_depth,
                    current_scc_id,
                    current_component
                ),
                finish_order.iter().rev().copied(),
                |
                    stack,
                    (
                        scc_ids,
                        sccs,
                        active_depth,
                        current_scc_id,
                        current_comp
                    ),
                    node
                | {
                    if *active_depth == 0 {
                        let (next_id, _slot) = sccs.reserve();
                        *current_scc_id = next_id;
                        current_comp.clear()
                    }

                    scc_ids.insert(node, *current_scc_id);
                    current_comp.push(node);

                    *active_depth += 1;

                    stack.push(reverse_edges[node.get()].iter().copied());
                },
                |
                    (
                        _scc_ids,
                        sccs,
                        active_depth,
                        current_scc,
                        current_comp
                    ),
                    _done_node
                | {
                    *active_depth -= 1;
                    if *active_depth == 0 {
                        let id = sccs.store(Scc(core::mem::take(current_comp)));
                        debug_assert_eq!(*current_scc, id);
                    }
                },
                total_items,
            );

            (scc_ids, sccs)
        };


        #[cold]
        #[inline(never)]
        fn build_cycle_for_component(
            component_definitions: &[MirDefId],
            forward_edges: &FilledArenaMap<MirDefId, HashMap<MirDefId, Span>>,
            total_items: usize,
        ) -> Cycle<Span> {
            algorithms::try_dfs_acyclic(
                (),
                component_definitions.iter().copied(),
                |stack, &mut (), node| {
                    let iter = forward_edges[node]
                        .iter()
                        .map(|(&id, &span)| (id, span));

                    stack.push(iter)
                },
                |&mut (), _| (),
                total_items
            ).unwrap_err()
        }

        let mut const_cycles: Vec<Cycle<Span>> = Vec::new();

        for (_id, scc) in scc_graph.iter() {
            let components = scc.0.as_slice();
            let component_contains_const = components
                .iter()
                .any(|&definition_id| {
                    matches!(self.get_mir_def(definition_id), MirDef::Const(_))
                });

            if !component_contains_const {
                continue;
            }


            match *components {
                [] => {},
                [one] => {
                    if let Some(span) = forward_edges[one].get(&one).copied() {
                        const_cycles.push(Cycle { path: vec![span] })
                    }
                },
                ref scc => const_cycles.push(build_cycle_for_component(
                    scc,
                    &forward_edges,
                    total_items,
                )),
            }
        }

        let scc_count = scc_graph.len();
        let mut scc_out: Box<[Vec<SccId>]> = make_slice(|_| vec![], scc_count);
        let mut indegree: Box<[HandleInt]> = slice![0; scc_count];

        let mut seen_edges: HashSet<(SccId, SccId)> = HashSet::default();

        for def in forward_edges.keys() {
            let def_scc = scc_id_for_def[def];
            for (&dep, _) in forward_edges[def].iter() {
                let dep_scc = scc_id_for_def[dep];
                if dep_scc == def_scc {
                    continue;
                }

                // edge dep_scc -> def_scc
                if seen_edges.insert((dep_scc, def_scc)) {
                    scc_out[dep_scc.get()].push(def_scc);
                    let indegree = &mut indegree[def_scc.get()];
                    *indegree += 1;
                }
            }
        }

        cfg_if! {
            if #[cfg(debug_assertions)] {
                struct SccQueueInner(
                    alloc::collections::BinaryHeap<(bool, core::cmp::Reverse<SccId>)>
                );

                impl SccQueueInner {
                    pub fn with_capacity(cap: usize) -> Self {
                        Self(alloc::collections::BinaryHeap::with_capacity(cap))
                    }

                    pub fn push(&mut self, is_constraint: bool, scc: SccId) {
                        self.0.push((is_constraint, core::cmp::Reverse(scc)))
                    }

                    pub fn pop(&mut self) -> Option<SccId> {
                        self.0.pop().map(|(_, core::cmp::Reverse(item))| item)
                    }
                }
            } else {
                struct SccQueueInner {
                    constraint_vec: Vec<SccId>,
                    normal_scc_vec: Vec<SccId>,
                }

                impl SccQueueInner {
                    pub fn with_capacity(cap: usize) -> Self {
                        Self {
                            // constraints always have 2 deps so they must at least be one third
                            // of all scc's
                            constraint_vec: Vec::with_capacity(cap / 3),
                            normal_scc_vec: Vec::with_capacity(cap),
                        }
                    }

                    pub fn push(&mut self, is_constraint: bool, scc: SccId) {
                        let vec = match is_constraint {
                            true => &mut self.constraint_vec,
                            false => &mut self.normal_scc_vec
                        };

                        vec.push(scc)
                    }

                    pub fn pop(&mut self) -> Option<SccId> {
                        self
                            .constraint_vec
                            .pop()
                            .or_else(|| self.normal_scc_vec.pop())
                    }
                }
            }
        }

        struct SccQueue<'a>(
            &'a Arena<Scc>,
            MirOrderer<'a>,
            SccQueueInner
        );

        impl<'a> SccQueue<'a> {
            pub fn with_capacity(scc: &'a Arena<Scc>, orderer: MirOrderer<'a>) -> Self {
                Self(
                    scc,
                    orderer,
                    SccQueueInner::with_capacity(scc.len())
                )
            }

            pub fn push(&mut self, scc: SccId) {
                let scc_ref = self.0[scc].0.as_slice();
                let is_constraint = if let &[one] = scc_ref
                    && let MirDef::Constraint(_) = self.1.get_mir_def(one)
                {
                    true
                } else {
                    false
                };

                self.2.push(is_constraint, scc)
            }

            pub fn pop(&mut self) -> Option<SccId> {
                self.2.pop()
            }
        }


        let mut queue = SccQueue::with_capacity(&scc_graph, MirOrderer { ..*self });
        for (scc_id, _) in scc_graph.iter() {
            if indegree[scc_id.get()] == 0 {
                queue.push(scc_id);
            }
        }

        let mut scc_topo: Vec<SccId> = Vec::with_capacity(scc_count);
        while let Some(scc) = queue.pop() {
            scc_topo.push(scc);
            for &to in &scc_out[scc.get()] {
                let indegree = &mut indegree[to.get()];
                *indegree -= 1;
                if *indegree == 0 {
                    queue.push(to);
                }
            }
        }

        debug_assert_eq!(scc_topo.len(), scc_count);

        let mut scc_graph = scc_graph;
        let mut emission_order: Vec<MirDefId> = Vec::with_capacity(total_items);
        for scc in scc_topo {
            let defs = scc_graph[scc].0.as_mut_slice();
            #[cfg(debug_assertions)]
            {
                defs.sort_unstable();
            }
            emission_order.extend_from_slice(defs);
        }

        debug_assert_eq!(emission_order.len(), total_items);

        (emission_order, const_cycles)
    }
}


fn fold_root(
    exprs: &mut Arena<SpannedExpr>,
    blocks: &Arena<Block>,
    root: ExprId,
) {
    let mut parent: Vec<Option<ExprId>> = vec![None; exprs.len()];
    let mut stack: Vec<(ExprId, bool)> = vec![(root, false)];

    while let Some((id, done)) = stack.pop() {
        if !done {
            stack.push((id, true));

            // Collect children (ExprId edges only) and push them.
            // NOTE: This signature only has `exprs`, so we cannot descend into `BlockId`
            // bodies; we still fold inside all ExprId-linked subexpressions.
            let mut push_child = |child: ExprId| {
                let idx = child.get();
                if parent[idx].is_none() {
                    parent[idx] = Some(id);
                }
                stack.push((child, false));
            };

            let mut push_block = |block: BlockId| {
                let Block { ref stmts, trailing_expr } = blocks[block];
                for stmt in stmts {
                    match *stmt {
                        Stmt::Let { local: _, initializer: Some(expr), span: _ }
                        | Stmt::Expression { expr, is_expr_stmt: _ } => {
                            push_child(expr)
                        }
                        Stmt::Let { initializer: None, .. } => {}
                    }
                }

                if let TrailingExpr::Trailing(expr) = trailing_expr {
                    push_child(expr)
                }
            };

            match exprs[id].expr {
                Expr::Assign { location, expr } => {
                    push_child(location);
                    push_child(expr);
                }
                Expr::BinOp { lhs, rhs, .. } => {
                    push_child(lhs);
                    push_child(rhs);
                }
                Expr::UnOp { expr, .. } => {
                    push_child(expr);
                }
                Expr::CastAs { expr, .. } => {
                    push_child(expr);
                }
                Expr::Call { callee, ref args } => {
                    push_child(callee);
                    for &a in args {
                        push_child(a);
                    }
                }
                Expr::Index { container, index } => {
                    push_child(container);
                    push_child(index);
                }
                Expr::Tuple(ref items) => {
                    for &e in items {
                        push_child(e);
                    }
                }
                Expr::ArraySplat { element, .. } => {
                    push_child(element);
                }
                Expr::Array(ref items) => {
                    for &e in items {
                        push_child(e);
                    }
                }
                Expr::Return(e) | Expr::Break(e) => {
                    push_child(e);
                }

                Expr::Block(block)
                | Expr::Loop(block) => push_block(block),

                Expr::If {
                    if_so,
                    ref else_if,
                    else_branch,
                } => {
                    let blocks = iter::once(if_so.body)
                        .chain(else_if.iter().map(|br| br.body))
                        .chain(else_branch);

                    for block in blocks {
                        push_block(block)
                    }

                    // We can fold in conditions; block bodies require `blocks`.
                    push_child(if_so.condition);
                    for br in else_if {
                        push_child(br.condition);
                    }
                }

                // No ExprId children reachable with only `exprs`:
                Expr::Error
                | Expr::Literal(_)
                | Expr::Const(_)
                | Expr::Function(_)
                | Expr::Local(_)
                | Expr::Continue => {}
            }

            continue;
        }

        let Expr::UnOp { op: UnOpKind::Neg, expr: first } = exprs[id].expr else {
            continue;
        };

        // If parent is also a negation, skip: only rewrite at the top-level neg in the chain.
        if let Some(p) = parent[id.get()]
            && let Expr::UnOp { op: UnOpKind::Neg, .. } = exprs[p].expr
        {
            continue;
        }

        // Count consecutive negations downwards.
        let mut negs: usize = 1;
        let mut cur: ExprId = first;

        while let Expr::UnOp { op: UnOpKind::Neg, expr: next } = exprs[cur].expr {
            negs += 1;
            cur = next;
        }

        // Must end at an integer literal to fold.
        let Expr::Literal(
            LiteralValue::Integer { negative, value, ty }
        ) = exprs[cur].expr else {
            continue;
        };

        let flip = !negs.is_multiple_of(2);
        let new_negative = negative ^ flip;
        // Rewrite ONLY the top-level negation node into the literal.
        exprs[id].expr = Expr::Literal(LiteralValue::Integer {
            negative: new_negative,
            value,
            ty
        });
    }
}


fn fold_literals(
    exprs: &mut Arena<SpannedExpr>,
    blocks: &Arena<Block>,
    functions: &Arena<FuncDef>,
    constants: &ConstantsEngine,
    compile_errors: &mut Vec<CompileError>
) {
    let _ = compile_errors;
    for (_, function) in functions.iter() {
        fold_root(exprs, blocks, function.body)
    }

    for (_, cnst) in constants.iter() {
        match cnst.expr {
            ConstExpr::ArrayLen(..) => {}
            ConstExpr::LateInit { expr, locals: _ } => fold_root(exprs, blocks, expr)
        }
    }
}

mod interpreter;

pub struct MirBuilder {
    const_value: ArenaMap<ConstEvalId, Scalar>,
}

pub struct Mir {

}


impl Mir {
    fn build(
        interner: &mut Interner,
        compile_errors: &mut Vec<CompileError>,
        hir: TypedHir,
    ) -> Result<Self, ()> {
        let hir = {
            let mut hir = hir;
            fold_literals(
                &mut hir.exprs,
                &hir.blocks,
                &hir.functions,
                &hir.const_exprs,
                compile_errors
            );
            // TODO: make sure all variables are initialized before use
            hir
        };
        let orderer = MirOrderer::new(&hir);
        let (order, cycles) = orderer
            .compute_order(compile_errors, interner);

        for cycle in cycles {
            compile_errors.push(CompileError::cycle_detected(cycle.path));
        }

        if !compile_errors.is_empty() {
            return Err(())
        }

        let mut builder = MirBuilder {
            const_value: hir.const_exprs.make_side_table(),
        };

        'parsing_items:
        for &id in order.iter() {
            match orderer.get_mir_def(id) {
                MirDef::Func(_func) => todo!("compile body"),
                MirDef::Constraint(id) => {
                    let (&constrains, &span) = hir.types.equal_constants.get_indexed(id);

                    let [one_id, two_id] = constrains.ids_equal();
                    let [one, two] = [
                        &hir.const_exprs[one_id],
                        &hir.const_exprs[two_id]
                    ];

                    let int_ty = {
                        let tys = [one.ty, two.ty].map(|ty| &hir.types[ty]);
                        match tys {
                            [&hir::Ty::Primitive(p1), &hir::Ty::Primitive(p2)] => {
                                if p1 != p2 {
                                    compile_errors.push(CompileError::type_mismatch(
                                        span,
                                        p1.as_str(),
                                        p2.as_str()
                                    ));
                                    continue 'parsing_items
                                }
                                match p1 {
                                    // no value will be found at either location
                                    PrimTy::Never => continue 'parsing_items,
                                    PrimTy::Bool => IntTy::U8,

                                    PrimTy::USIZE => IntTy::USIZE,
                                    PrimTy::U64 => IntTy::U64,
                                    PrimTy::U32 => IntTy::U32,
                                    PrimTy::U16 => IntTy::U16,
                                    PrimTy::U8 => IntTy::U8,

                                    PrimTy::ISIZE => IntTy::ISIZE,
                                    PrimTy::I64 => IntTy::I64,
                                    PrimTy::I32 => IntTy::I32,
                                    PrimTy::I16 => IntTy::I16,
                                    PrimTy::I8 => IntTy::I8,
                                }
                            },
                            _ => {
                                let (main_span, second) = span.as_two_spans();
                                compile_errors.push(CompileError::custom_full(
                                    main_span,
                                    "invalid constraint",
                                    "constraints only support integer types and booleans",
                                    second.map(|spn| (spn, "invalid constraint"))
                                ));
                                continue 'parsing_items
                            }
                        }
                    };

                    let vals = builder
                        .const_value
                        .get(one_id)
                        .and_then(|&one| {
                            Some((one, builder.const_value.get(two_id).copied()?))
                        });

                    let Some((val1, val2)) = vals else {
                        // something else errored
                        continue 'parsing_items
                    };

                    if val1.ieq(val2, int_ty) {
                        let (span, second) = span.as_two_spans();
                        let args_fmt = format_args!(
                            "mismatched values {} and {}",
                            val1.idisplay(int_ty),
                            val2.idisplay(int_ty)
                        );
                        let args_nofmt = format_args!("this value");
                        compile_errors.push(CompileError::custom_full(
                            span,
                            "unfulfilled constraint",
                            if second.is_none() { args_fmt } else { args_nofmt },
                            second.map(|spn| (spn, "is not equal to this value"))
                        ))
                    }
                },
                MirDef::Const(cnst) => {
                    let value = match hir.const_exprs[cnst].expr {
                        ConstExpr::ArrayLen(val, span) => {
                            let res = u128::try_from(val)
                                .map_err(|_| ParseIntLiteralError::NEW)
                                .and_then(|val| Scalar::parse_int_literal(
                                    false,
                                    val,
                                    IntTy::USIZE
                                ));

                            match res {
                                Ok(x) => x,
                                Err(_err) => {
                                    compile_errors.push(CompileError::custom(
                                        span,
                                        "array too long",
                                        "this array's length is too long to fit in the targets usize"
                                    ));
                                    continue 'parsing_items
                                }
                            }
                        },
                        ConstExpr::LateInit {
                            expr: _,
                            locals: _,
                        } => todo!("compile body and run"),
                    };

                    builder.const_value.insert(cnst, value);
                }
            };
        }

        Err(())
    }
}


pub fn make_mir(
    interner: &mut Interner,
    compile_errors: &mut Vec<CompileError>,
    hir: TypedHir,
) -> Result<Mir, ()> {
    Mir::build(interner, compile_errors, hir)
}
