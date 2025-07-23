use oval::compile::error::ErrorCache;
use oval::compile::interner::Interner;
use oval::compile::source_map::SourceMap;
use oval::compile::syntax::parse_file;

fn main() -> eyre::Result<()> {
    let mut interner = Interner::new();
    let module_path = interner.register_path("tests::function")?;

    let source_map = SourceMap::builder()
        .file_module(module_path, "./oval/test-files/function.oval")?
        .build(&interner)
        .map_err(|err| eyre::Error::msg(err.to_string()))?;

    let mut error_cache = ErrorCache::new(&source_map);
    for source in source_map.modules() {
        let file = match source
            .tokenize()
            .and_then(|stream| parse_file(stream, &mut interner))
        {
            Ok(stream) => stream,
            Err(err) => {
                for report in err.error_reports() {
                    report.eprint((&mut error_cache, &interner))?
                }

                return Ok(());
            }
        };

        dbg!(file);
    }

    Ok(())
}
