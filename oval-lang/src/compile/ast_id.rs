
#[derive(Copy, Clone, PartialOrd, PartialEq)]
#[repr(transparent)]
pub struct AstId {
    addr: usize,
}

impl AstId {
    pub fn new<T>(node: &T) -> Self {
        let addr = (node as *const T).addr();
        Self { addr }
    }
}
