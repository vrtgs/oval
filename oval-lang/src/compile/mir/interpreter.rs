use crate::compile::mir::Mir;
use crate::spanned::Span;
use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;

enum TrapKind {
    IndexOutOfBounds {
        length: usize,
        requested_index: usize
    }
}

struct TrapInner {
    stack_trace: Vec<Span>,
    kind: TrapKind
}

pub struct Trap(Box<TrapInner>);

impl Trap {
    fn new(stack_trace: Vec<Span>, kind: TrapKind) -> Self {
        Self(Box::new(TrapInner {
            stack_trace,
            kind,
        }))
    }

    #[cold]
    #[inline(never)]
    pub fn index_out_of_bounds(
        stack_trace: Vec<Span>,
        length: usize,
        requested_index: usize
    ) -> Self {
        assert!(requested_index >= length);
        Self::new(stack_trace, TrapKind::IndexOutOfBounds { 
            requested_index,
            length
        })
    }
}


struct CallFrame {
    span: Span
}

struct InterpreterUntyped<'a> {
    mir: &'a Mir,
    call_stack: Vec<CallFrame>,
    fuel: Option<u64>
}

impl<'a> InterpreterUntyped<'a> {
    fn new(mir: &'a Mir) -> Self {
        Self {
            mir,
            call_stack: vec![],
            fuel: None
        }
    }

    fn with_fuel(self, fuel: u64) -> Self {
        Self {
            fuel: Some(fuel),
            ..self
        }
    }
}

pub struct InterpreterTyped<'a, const CTFE: bool>(InterpreterUntyped<'a>);

type Interpreter<'a> = InterpreterTyped<'a, false>;
type CTFEInterpreter<'a> = InterpreterTyped<'a, true>;

impl<'a> Interpreter<'a> {
    pub fn new(mir: &'a Mir) -> Self {
        Self(InterpreterUntyped::new(mir))
    }
}

impl<'a> CTFEInterpreter<'a> {
    pub fn new(mir: &'a Mir) -> Self {
        Self(InterpreterUntyped::new(mir).with_fuel(u16::MAX.into()))
    }
}
