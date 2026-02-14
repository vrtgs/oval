use oval_lang::interner::Interner;
use oval_lang::parser::parse;

mod fmt_ast;

#[cfg(not(miri))]
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

fn main() -> eyre::Result<()> {
    let mut interner = Interner::new();
    let source = &*std::fs::read_to_string("./ovalc/test-files/const-eval.oval")?;
    let result = parse(&mut interner, source);

    if result.errors.is_none() {
        println!("{}", fmt_ast::display_module(&result.module, &interner));
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
