use crate::compile::build_hir::Type;
use alloc::boxed::Box;

#[repr(transparent)]
pub struct FunctionSignature([Type]);

impl FunctionSignature {
    const fn args_ret(&self) -> (&[Type], &Type) {
        let (ret, args) = unsafe { self.0.split_last().unwrap_unchecked() };
        (args, ret)
    }

    pub const fn args(&self) -> &[Type] {
        self.args_ret().0
    }

    pub const fn ret(&self) -> &Type {
        self.args_ret().1
    }

    const fn args_ret_mut(&mut self) -> (&mut [Type], &mut Type) {
        let (ret, args) = unsafe { self.0.split_last_mut().unwrap_unchecked() };
        (args, ret)
    }

    pub const fn args_mut(&mut self) -> &mut [Type] {
        self.args_ret_mut().0
    }

    pub const fn ret_mut(&mut self) -> &mut Type {
        self.args_ret_mut().1
    }

    pub fn from_box(boxed: Box<[Type]>) -> Box<FunctionSignature> {
        assert!(!boxed.is_empty());
        // Safety:
        unsafe { Box::from_raw(Box::into_raw(boxed) as *mut FunctionSignature) }
    }
}
