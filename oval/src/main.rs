use oval::compile::{SourceErrorCache, SourceMap};

fn main() -> eyre::Result<()> {
    let source_map = SourceMap::builder()
        .file_module("tests::function".parse()?,"./oval/test-files/function.oval")?
        .build()?;
    
    let mut error_cache = SourceErrorCache::new(&source_map);
    
    for source in source_map.modules() {
        let stream = match source.tokenize().into_stream() {
            Ok(stream) => stream,
            Err(err) => {
                for report in err.error_reports() {
                    report.eprint(&mut error_cache)?
                }
                
                return Ok(())
            }
        };
        
        for token in stream.stream() {
            dbg!(token);
        }
    }
    
    Ok(())
}
