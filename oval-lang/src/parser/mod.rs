use crate::ast::OvalModule;
use crate::parser::sealed::ParseOvalModuleSealed;
use alloc::vec;
use chumsky::extra::SimpleState;
use chumsky::Parser;
use core::cell::RefCell;

mod parser_impl;
use crate::hashed::HashSet;
use crate::parser::parser_impl::{ParserErrorWrapper, SyntaxError};
use crate::spanned::Span;
use crate::tokens::{Tokenizer, TokenizerError};
pub use parser_impl::ParseErrors;

pub(crate) use parser_impl::{
    static_parser, static_unsized_parser, AstParse, InputTape, OvalParser, ParserData, ParserState,
};

use crate::interner::Interner;
#[allow(unused_imports)]
pub(crate) use parser_impl::static_parser_inner;

mod sealed {
    use super::*;

    pub trait ParseOvalModuleSealed {
        fn parse(self, interner: &mut Interner) -> ParseResult;
    }
}

#[derive(Debug)]
pub struct ParseResult {
    pub module: OvalModule,
    pub errors: Option<ParseErrors>,
}

impl ParseResult {
    pub fn into_result(self) -> Result<OvalModule, ParseErrors> {
        match self.errors {
            Some(err) => Err(err),
            None => Ok(self.module),
        }
    }
}

pub trait ParseOvalModule: ParseOvalModuleSealed {}
impl<T: ParseOvalModuleSealed> ParseOvalModule for T {}

impl ParseOvalModuleSealed for &str {
    fn parse(self, interner: &mut Interner) -> ParseResult {
        let len = self.len();
        let eoi = Span::new(len, len);
        let tokenizer_errors = RefCell::new(HashSet::default());

        let input = chumsky::input::IterInput::new(
            Tokenizer::new(self).filter_map(|val| match val {
                Ok(token) => Some((token.kind, token.span)),
                Err(err) => {
                    tokenizer_errors.borrow_mut().insert(err.0);
                    None
                }
            }),
            eoi,
        );

        let mut state: SimpleState<ParserState<_>> = SimpleState(ParserState {
            interner,
            text: self,
            produced_errors: vec![],
        });

        type Extra<'src> = chumsky::extra::Full<
            ParserErrorWrapper<SyntaxError>,
            SimpleState<ParserState<'src, ParserErrorWrapper<SyntaxError>>>,
            (),
        >;

        let result = OvalModule::parser::<_, Extra>().parse_with_state(input, &mut state);

        let (file, errors) = result.into_output_errors();

        let SimpleState(state) = state;

        let recoverable_errors = state.produced_errors.into_iter().map(|err| err.0).chain({
            tokenizer_errors
                .into_inner()
                .into_iter()
                .map(TokenizerError)
                .map(SyntaxError::from)
        });

        let fatal_errors = errors.into_iter().map(|err| err.0);

        let error = ParseErrors::new(fatal_errors, recoverable_errors);

        if file.is_none() {
            assert!(
                error.is_some(),
                "failed to produce a file; but got no errors"
            )
        }

        ParseResult {
            module: file.unwrap_or(
                const {
                    OvalModule {
                        attributes: vec![],
                        items: vec![],
                    }
                },
            ),
            errors: error,
        }
    }
}

pub fn parse<T: ParseOvalModule>(interner: &mut Interner, to_ast: T) -> ParseResult {
    to_ast.parse(interner)
}
