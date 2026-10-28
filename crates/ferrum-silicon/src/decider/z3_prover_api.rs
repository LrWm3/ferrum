// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

//! In-process Z3 session control from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/Z3ProverAPI.scala.
//!
//! Status: explicit native driver contract, buffered preamble, declarations, assumptions,
//! scope, timeout, checking and push/pop assertions implemented. The linked Z3 driver,
//! source option parsing, trigger-repair retry, soft-constraint assertion, model extraction,
//! fresh names and the full `Prover` adapter remain pending; none are emulated as success.

use crate::decider::term_to_z3_api_converter::{
    NativeConversionError, NativeDeclaration, NativeOp, TermToZ3ApiConverter, Z3NativeContext,
};
use crate::interfaces::decider::prover::SatResult;
use crate::state::terms::{Declaration, Term};

/// Implemented by a linked native solver. Every handle belongs to this context; parsing must
/// use the paired sort and function symbols exactly in the supplied order.
pub trait NativeZ3Solver: Z3NativeContext {
    fn parse_and_add_preamble(
        &mut self,
        commands: &[String],
        sorts: &[(String, Self::Sort)],
        functions: &[(String, Self::Function)],
    ) -> Result<(), Self::Error>;
    fn add(&mut self, term: &Self::Expr) -> Result<(), Self::Error>;
    fn push(&mut self) -> Result<(), Self::Error>;
    fn pop(&mut self, n: usize) -> Result<(), Self::Error>;
    fn set_limit(&mut self, resource_limit: bool, value: i64) -> Result<(), Self::Error>;
    fn check(&mut self) -> Result<SatResult, Self::Error>;
}
#[derive(Clone, Copy, Debug)]
pub struct ApiTimeoutSettings {
    pub default_timeout_ms: i32,
    pub use_time_bounds: bool,
    pub resources_per_millisecond: i32,
}
#[derive(Debug)]
pub enum ApiProverError<E> {
    Conversion(NativeConversionError<E>),
    Driver(E),
    PreambleEnded,
    ScopeUnderflow,
    /// A check failed and scope restoration also failed; retain both errors.
    CheckAndRestore {
        check: E,
        restore: E,
    },
}
impl<E> From<NativeConversionError<E>> for ApiProverError<E> {
    fn from(value: NativeConversionError<E>) -> Self {
        Self::Conversion(value)
    }
}
type ApiResult<C, T> = Result<T, ApiProverError<<C as Z3NativeContext>::Error>>;

pub struct Z3ApiSession<C: NativeZ3Solver> {
    pub converter: TermToZ3ApiConverter<C>,
    timeout: ApiTimeoutSettings,
    last_timeout: Option<i32>,
    preamble_over: bool,
    preamble_parsed: bool,
    preamble: Vec<String>,
    assumptions: Vec<C::Expr>,
    sorts: Vec<(String, C::Sort)>,
    functions: Vec<(String, C::Function)>,
    declarations: Vec<Declaration>,
    depth: usize,
}
impl<C: NativeZ3Solver> Z3ApiSession<C> {
    pub fn new(converter: TermToZ3ApiConverter<C>, timeout: ApiTimeoutSettings) -> Self {
        Self {
            converter,
            timeout,
            last_timeout: None,
            preamble_over: false,
            preamble_parsed: false,
            preamble: Vec::new(),
            assumptions: Vec::new(),
            sorts: Vec::new(),
            functions: Vec::new(),
            declarations: Vec::new(),
            depth: 0,
        }
    }
    pub fn emit(&mut self, command: String) -> ApiResult<C, ()> {
        if self.preamble_over || self.preamble_parsed {
            return Err(ApiProverError::PreambleEnded);
        }
        self.preamble.push(command);
        Ok(())
    }
    pub fn declare(&mut self, declaration: &Declaration) -> ApiResult<C, ()> {
        match self.converter.convert_declaration(declaration)? {
            NativeDeclaration::Sort {
                name: Some(name),
                sort,
            } => {
                if !self.sorts.iter().any(|(_, old)| old == &sort) {
                    self.sorts.push((name, sort));
                }
            }
            NativeDeclaration::Sort { name: None, .. } | NativeDeclaration::ExpandedMacro => (),
            NativeDeclaration::Function { name, function } => {
                if !self.functions.iter().any(|(_, old)| old == &function) {
                    self.functions.push((name, function));
                }
            }
        }
        self.declarations.push(declaration.clone());
        Ok(())
    }
    pub fn assume(&mut self, term: &Term) -> ApiResult<C, ()> {
        let expr = self.converter.convert_term(term)?;
        if self.preamble_over {
            self.converter
                .context
                .add(&expr)
                .map_err(ApiProverError::Driver)?;
        } else {
            if !self.assumptions.contains(&expr) {
                self.assumptions.push(expr);
            }
        }
        Ok(())
    }
    pub fn end_preamble(&mut self) -> ApiResult<C, ()> {
        if !self.preamble_over {
            if !self.preamble_parsed {
                self.converter
                    .context
                    .parse_and_add_preamble(&self.preamble, &self.sorts, &self.functions)
                    .map_err(ApiProverError::Driver)?;
                self.preamble_parsed = true;
            }
            // Remove each assumption only after it is accepted, so an error cannot silently drop it.
            while let Some(expr) = self.assumptions.first() {
                self.converter
                    .context
                    .add(expr)
                    .map_err(ApiProverError::Driver)?;
                self.assumptions.remove(0);
            }
            self.preamble_over = true;
        }
        Ok(())
    }
    fn set_timeout(&mut self, timeout_ms: Option<i32>) -> ApiResult<C, ()> {
        let effective = timeout_ms.unwrap_or(self.timeout.default_timeout_ms);
        if self.last_timeout != Some(effective) {
            let resource = !self.timeout.use_time_bounds;
            let value = if resource {
                i64::from(effective) * i64::from(self.timeout.resources_per_millisecond)
            } else {
                i64::from(effective)
            };
            self.converter
                .context
                .set_limit(resource, value)
                .map_err(ApiProverError::Driver)?;
            self.last_timeout = Some(effective);
        }
        Ok(())
    }
    pub fn push(&mut self, n: usize, timeout_ms: Option<i32>) -> ApiResult<C, ()> {
        self.end_preamble()?;
        self.set_timeout(timeout_ms)?;
        for _ in 0..n {
            self.converter
                .context
                .push()
                .map_err(ApiProverError::Driver)?;
            self.depth += 1;
        }
        Ok(())
    }
    pub fn pop(&mut self, n: usize) -> ApiResult<C, ()> {
        self.end_preamble()?;
        if n > self.depth {
            return Err(ApiProverError::ScopeUnderflow);
        }
        self.converter
            .context
            .pop(n)
            .map_err(ApiProverError::Driver)?;
        self.depth -= n;
        Ok(())
    }
    pub fn check(&mut self, timeout_ms: Option<i32>) -> ApiResult<C, SatResult> {
        self.end_preamble()?;
        self.set_timeout(timeout_ms)?;
        self.converter
            .context
            .check()
            .map_err(ApiProverError::Driver)
    }
    /// Source push/pop assertion checks the negated goal and proves it only on UNSAT.
    /// Model and unknown-reason retrieval are deliberately left to the native driver adapter.
    pub fn assert_push_pop(&mut self, goal: &Term, timeout_ms: Option<i32>) -> ApiResult<C, bool> {
        self.end_preamble()?;
        let expr = self.converter.convert_term(goal)?;
        let negated = self
            .converter
            .context
            .builtin(NativeOp::Not, &[expr])
            .map_err(ApiProverError::Driver)?;
        self.push(1, None)?;
        let checked = (|| {
            self.set_timeout(timeout_ms)?;
            self.converter
                .context
                .add(&negated)
                .map_err(ApiProverError::Driver)?;
            self.converter
                .context
                .check()
                .map_err(ApiProverError::Driver)
        })();
        let restored = self.pop(1);
        match (checked, restored) {
            (Ok(result), Ok(())) => Ok(result == SatResult::Unsat),
            (Err(ApiProverError::Driver(check)), Err(ApiProverError::Driver(restore))) => {
                Err(ApiProverError::CheckAndRestore { check, restore })
            }
            (Err(error), _) | (Ok(_), Err(error)) => Err(error),
        }
    }
    pub fn scope_depth(&self) -> usize {
        self.depth
    }
    pub fn declarations(&self) -> &[Declaration] {
        &self.declarations
    }
    pub fn emissions(&self) -> &[String] {
        &self.preamble
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decider::term_to_z3_api_converter::{NativeLiteral, NativeSort};
    use crate::state::identifiers::Identifier;
    use crate::state::terms::{Quantifier, Sort, TermFactory, TermOptions};
    #[derive(Default)]
    struct Fake {
        result: Option<SatResult>,
        depth: usize,
        parses: usize,
    }
    impl Z3NativeContext for Fake {
        type Sort = String;
        type Expr = String;
        type Function = String;
        type Error = ();
        fn sort(&mut self, sort: NativeSort) -> Result<String, ()> {
            Ok(format!("{sort:?}"))
        }
        fn function(&mut self, name: &str, _: &[String], _: &String) -> Result<String, ()> {
            Ok(name.into())
        }
        fn literal(&mut self, l: NativeLiteral, _: &String) -> Result<String, ()> {
            Ok(format!("{l:?}"))
        }
        fn constant(&mut self, name: &str, _: &String) -> Result<String, ()> {
            Ok(name.into())
        }
        fn builtin(&mut self, op: NativeOp, args: &[String]) -> Result<String, ()> {
            Ok(format!("{op:?}{args:?}"))
        }
        fn application(
            &mut self,
            name: &str,
            _: &[String],
            _: &String,
            _: &[String],
            _: bool,
        ) -> Result<String, ()> {
            Ok(name.into())
        }
        fn quantifier(
            &mut self,
            _: Quantifier,
            _: &[String],
            _: &String,
            _: &[Vec<String>],
            _: &str,
            _: i32,
        ) -> Result<String, ()> {
            Ok("quantifier".into())
        }
    }
    impl NativeZ3Solver for Fake {
        fn parse_and_add_preamble(
            &mut self,
            _: &[String],
            _: &[(String, String)],
            _: &[(String, String)],
        ) -> Result<(), ()> {
            self.parses += 1;
            Ok(())
        }
        fn add(&mut self, _: &String) -> Result<(), ()> {
            Ok(())
        }
        fn push(&mut self) -> Result<(), ()> {
            self.depth += 1;
            Ok(())
        }
        fn pop(&mut self, n: usize) -> Result<(), ()> {
            self.depth -= n;
            Ok(())
        }
        fn set_limit(&mut self, _: bool, _: i64) -> Result<(), ()> {
            Ok(())
        }
        fn check(&mut self) -> Result<SatResult, ()> {
            Ok(self.result.unwrap())
        }
    }
    #[test]
    fn push_pop_assertion_never_proves_unknown_and_restores_scope() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let goal = factory.var(Identifier::new("p"), Sort::Bool, false);
        let converter = TermToZ3ApiConverter::new(
            Fake {
                result: Some(SatResult::Unknown),
                ..Fake::default()
            },
            factory,
        );
        let mut session = Z3ApiSession::new(
            converter,
            ApiTimeoutSettings {
                default_timeout_ms: 0,
                use_time_bounds: true,
                resources_per_millisecond: 1,
            },
        );
        session.emit("(set-logic ALL)".into()).unwrap();
        assert!(!session.assert_push_pop(&goal, None).unwrap());
        assert_eq!(session.scope_depth(), 0);
        assert_eq!(session.converter.context.depth, 0);
        assert_eq!(session.converter.context.parses, 1);
        session.converter.context.result = Some(SatResult::Unsat);
        assert!(session.assert_push_pop(&goal, Some(10)).unwrap());
        assert_eq!(session.converter.context.parses, 1);
    }
}
