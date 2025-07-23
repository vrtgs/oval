use chumsky::prelude::SimpleSpan;

pub mod interner;
pub mod error;
pub mod hir;
pub mod source;
pub mod source_map;
pub mod syntax;
pub mod tokenizer;

#[derive(Debug, Copy, Clone)]
pub struct Spanned<T, S = SimpleSpan> {
    pub span: S,
    pub value: T,
}
