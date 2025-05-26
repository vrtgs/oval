use crate::parser::ParserContext;

pub mod parser;

fn main() -> eyre::Result<()> {
    let file_name = "./test.oval";
    let mut contex = ParserContext::new();
    match parser::parse_file(file_name, &mut contex) {
        Ok(_) => todo!("Todo interpret input"),
        Err(error) => {
            let file_name = error.file_name();
            let source = error.source();

            for report in error.error_reports() {
                report.eprint((file_name, source))?
            }
            return Ok(())
        }
    };
    
    Ok(())
}
