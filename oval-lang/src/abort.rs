
#[cfg_attr(feature = "std", inline(always))]
#[cold]
pub fn abort() -> ! {
    #[cfg(not(feature = "std"))]
    {
        // Panicking while panicking is defined by Rust to result in an abort.
        struct Panic;

        impl Drop for Panic {
            fn drop(&mut self) {
                panic!("aborting");
            }
        }

        let _panic = Panic;
        panic!("aborting")
    }

    #[cfg(feature = "std")]
    {
        extern crate std;
        std::process::abort()
    }
}


pub struct AbortGuard(());

impl AbortGuard {
    pub const fn new() -> Self {
        Self(())
    }

    pub const fn disarm(self) {
        core::mem::forget(self)
    }
}

impl Drop for AbortGuard {
    fn drop(&mut self) {
        abort()
    }
}