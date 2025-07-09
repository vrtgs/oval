use chumsky::prelude::SimpleSpan;

pub mod source_file;
pub mod tokenizer;
pub mod error;
pub mod parser;
pub mod source_map;
pub mod compiler;
pub mod interner;


#[derive(Debug, Copy, Clone)]
pub struct Spanned<T, S = SimpleSpan> {
    pub span: S,
    pub value: T
}
