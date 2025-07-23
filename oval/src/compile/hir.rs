use crate::compile::hir::item::Item;
use crate::compile::source::Source;
use crate::compile::source_map::SourceMap;
use crate::compile::syntax::OvalFile;
use alloc::vec::Vec;

mod item;
mod scoped;
mod r#type;

pub struct HIR<'a> {
    pub source: Source<'a>,
    pub items: Vec<Item>,
}

pub fn parse<'a>(files: &SourceMap<'a>, file: OvalFile<'a>) -> HIR<'a> {
    assert!(files.contains_module(file.source.id()));

    todo!()
}
