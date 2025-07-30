use crate::compile::hir::item::Item;
use crate::compile::source_map::SourceMap;
use alloc::vec::Vec;
use alloc::vec;
use crate::compile;
use crate::compile::interner::Interner;
use crate::compile::syntax::{parse_file, OvalFile};

mod item;
mod scoped;
mod r#type;

pub struct HIR<'a> {
    pub sources: SourceMap<'a>,
    pub items: Vec<Item>,
}

pub fn parse<'a>(sources: &SourceMap<'a>, interner: &mut Interner) -> Result<HIR<'a>, compile::error::Error<'a>> {
    let Ok([file]) = <[_; 1]>::try_from(sources.modules().collect::<Vec<_>>()) else {
        todo!("more than one file")
    };

    let parsed: OvalFile<'a> = file
        .tokenize()
        .and_then(|stream| parse_file(stream, interner))?;


    let hir_items = vec![];

    for item in parsed.items {

    }

    Ok(HIR {
        sources: sources.clone(),
        items: hir_items,
    })
}
