use oval::interner::Interner;
use oval::parser::parse;

mod fmt_ast;

fn main() -> eyre::Result<()> {
    let mut interner = Interner::new();
    let source = include_str!("../test-files/function.oval");
    let result = parse(&mut interner, source);

    match oval::compile::verify(result, &mut interner) {
        Err(err) => {
            let source = ariadne::Source::from(source);
            for report in err.reports() {
                report.eprint(&source)?
            }

            std::process::exit(-1);
        }
        Ok(module) => println!("{}", fmt_ast::display_module(&module, &interner)),
    }



    Ok(())
}
