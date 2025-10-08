use oval_lang::interner::Interner;
use oval_lang::parser::parse;

mod fmt_ast;

fn main() -> eyre::Result<()> {
    let mut interner = Interner::new();
    let source = include_str!("../test-files/function.oval");
    let result = parse(&mut interner, source);

    if core::hint::black_box(false) {
        // dont warn about dead code
        let _ = core::hint::black_box(fmt_ast::display_module);
    }

    let _module = match oval_lang::compile::compile(&mut interner, result) {
        Err(err) => {
            let source = ariadne::Source::from(source);
            for report in err.reports() {
                report.eprint(&source)?
            }

            std::process::exit(-1)
        }
        Ok(module) => module,
    };

    todo!()
}
