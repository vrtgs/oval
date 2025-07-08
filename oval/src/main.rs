use oval::compile::compiler::Compiler;
use oval::compile::error::ErrorCache;
use oval::compile::parser::parse;
use oval::compile::source_map::SourceMap;

fn main() -> eyre::Result<()> {
    let mut compiler = Compiler::new();
    let module_path = compiler.register_path("tests::function")?;

    let source_map = SourceMap::builder()
        .file_module(module_path,"./oval/test-files/function.oval")?
        .build(&compiler)
        .map_err(|err| eyre::Error::msg(err.to_string()))?;


    let mut error_cache = ErrorCache::new(&source_map);
    for source in source_map.modules() {
        let file = match source.tokenize().into_stream().and_then(|stream| parse(&mut compiler, stream)) {
            Ok(stream) => stream,
            Err(err) => {
                for report in err.error_reports() {
                    report.eprint((&mut error_cache, &compiler))?
                }

                return Ok(())
            }
        };

        dbg!(file);
    }
    
    Ok(())
}
