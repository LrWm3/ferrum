//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/CfgSupporter.scala
//!
//! Purpose:
//! Verify a supplied Silver CFG using symbolic execution.
//!
//! Planned Rust structure:
//! Port CfgVerificationUnit, DefaultCfgVerificationUnitProvider and cfgSupporter
//! analyze/units/verify/lifecycle.
//!
//! Behavior to preserve:
//! Initialize fresh store, empty heap, old heaps and method CFG; optionally print DOT, execute
//! locally and return one verification result. Upstream analyze is unimplemented; do not represent
//! it as successful.
//!
//! Integration:
//! rules::{execution_flow_controller,executor}, state::{state,store}, verifier and Silver CFG.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for state isolation and lifecycle.
//!
//! Open decisions:
//! Agree on CFG unit discovery and verifier ownership with verifier and method_supporter.
//!
//! Status: partial; externally supplied CFG verification and source unsupported analysis
//! behavior implemented. Concrete executor, scope, solver and output services remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::interfaces::verification::VerificationResult;
use crate::state::heap::ListBackedHeap;
use crate::state::state::State;
use ferrum_silver::cfg::silver::silver_cfg::SilverCfg;
use std::sync::Arc;

pub trait CfgVerificationServices<P, D, J, V>: Sized {
    type Error;
    fn empty_cfg_heap(
        &mut self,
        state: &State<P, D, J>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error>;
    fn output_cfg(&mut self, cfg: &SilverCfg) -> Result<(), Self::Error>;
    fn cfg_locally(
        &mut self,
        state: State<P, D, J>,
        action: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, CfgVerificationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, CfgVerificationError<Self::Error>>;
    fn execute_cfg(
        &mut self,
        state: State<P, D, J>,
        cfg: &SilverCfg,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            VerificationResult<V>,
            CfgVerificationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, CfgVerificationError<Self::Error>>;
    /// Execute a standalone CFG whose terminal is source Success.
    fn execute_cfg_standalone(
        &mut self,
        state: State<P, D, J>,
        cfg: &SilverCfg,
    ) -> Result<VerificationResult<V>, CfgVerificationError<Self::Error>> {
        self.execute_cfg(state, cfg, &mut |_, _| Ok(VerificationResult::success()))
    }
}
#[derive(Debug)]
pub enum CfgVerificationError<E> {
    UnsupportedAnalysis,
    Service(E),
}
/// Upstream's program analysis is explicitly unimplemented.
pub fn analyze_cfgs<E>(
    _: &ferrum_silver::ast::program::Program,
) -> Result<Vec<Arc<SilverCfg>>, CfgVerificationError<E>> {
    Err(CfgVerificationError::UnsupportedAnalysis)
}
/// Execute an externally supplied CFG in a local scope with an empty store and heap.
pub fn verify_cfg<P, D, J: Clone, V, C: CfgVerificationServices<P, D, J, V>>(
    context: &mut C,
    mut state: State<P, D, J>,
    cfg: Arc<SilverCfg>,
) -> Result<Vec<VerificationResult<V>>, CfgVerificationError<C::Error>> {
    state.g = Arc::new(crate::state::store::MapBackedStore::new());
    state.h = context
        .empty_cfg_heap(&state)
        .map_err(CfgVerificationError::Service)?;
    state.old_heaps = Default::default();
    state.method_cfg = Some(cfg.clone());
    context
        .output_cfg(&cfg)
        .map_err(CfgVerificationError::Service)?;
    let result = context.cfg_locally(state, &mut |context, state| {
        context.execute_cfg_standalone(state, &cfg)
    })?;
    Ok(vec![result])
}

#[cfg(test)]
mod standalone_terminal_tests {
    use super::*;
    use crate::state::terms::{TermFactory, TermOptions};
    use ferrum_silver::ast::{
        program::Program,
        statement::{Stmt, StmtKind},
    };

    #[derive(Default)]
    struct Service {
        fail: bool,
        locally_entered: usize,
        locally_finished: usize,
        executions: usize,
    }
    impl CfgVerificationServices<(), (), (), ()> for Service {
        type Error = &'static str;
        fn empty_cfg_heap(
            &mut self,
            _: &State<(), (), ()>,
        ) -> Result<Arc<ListBackedHeap>, Self::Error> {
            Ok(Arc::new(ListBackedHeap::new()))
        }
        fn output_cfg(&mut self, _: &SilverCfg) -> Result<(), Self::Error> {
            Ok(())
        }
        fn cfg_locally(
            &mut self,
            state: State<(), (), ()>,
            action: &mut dyn FnMut(
                &mut Self,
                State<(), (), ()>,
            ) -> Result<
                VerificationResult<()>,
                CfgVerificationError<Self::Error>,
            >,
        ) -> Result<VerificationResult<()>, CfgVerificationError<Self::Error>> {
            self.locally_entered += 1;
            let result = action(self, state);
            self.locally_finished += 1;
            result
        }
        fn execute_cfg(
            &mut self,
            state: State<(), (), ()>,
            _: &SilverCfg,
            continuation: &mut dyn FnMut(
                &mut Self,
                State<(), (), ()>,
            ) -> Result<
                VerificationResult<()>,
                CfgVerificationError<Self::Error>,
            >,
        ) -> Result<VerificationResult<()>, CfgVerificationError<Self::Error>> {
            self.executions += 1;
            if self.fail {
                Err(CfgVerificationError::Service("execute"))
            } else {
                continuation(self, state)
            }
        }
    }
    #[test]
    fn generic_standalone_terminal_keeps_local_scope_completion() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Default::default(),
        );
        let state = State::new(
            program,
            Default::default(),
            Default::default(),
            (),
            &factory,
            false,
            false,
        );
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![],
                declarations: vec![],
            },
            Default::default(),
        );
        let cfg = Arc::new(
            ferrum_silver::cfg::silver::cfg_generator::statement_to_cfg(&body, true, true).unwrap(),
        );
        let mut service = Service::default();
        let result = verify_cfg(&mut service, state.clone(), cfg.clone()).unwrap();
        assert_eq!(result.len(), 1);
        assert!(!result[0].is_fatal());
        service.fail = true;
        assert!(matches!(
            verify_cfg(&mut service, state, cfg),
            Err(CfgVerificationError::Service("execute"))
        ));
        assert_eq!(
            (
                service.locally_entered,
                service.locally_finished,
                service.executions
            ),
            (2, 2, 2)
        );
    }
}
