//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Brancher.scala
//!
//! Purpose:
//! Split symbolic execution on a condition with optional parallel else branch.
//!
//! Planned Rust structure:
//! BranchingRules and brancher.branch perform feasibility checks, construct then/else tasks,
//! preserve solver scopes, report branch failures and combine results.
//!
//! Behavior to preserve:
//! Skip feasibility checks for short-circuit conjunctions or conditions containing quantified
//! variables, excluding wand snapshot variables; otherwise check negation first. If then is
//! infeasible, assume else feasible without a second check; otherwise check the condition. Represent
//! skipped paths as Unreachable. Execute then before waiting for else; synchronous future
//! defers else, while parallel mode transfers path conditions, declarations and prover options to
//! worker. Restore worker/current options and path conditions as needed, wait even after terminal
//! failure when parallel, propagate worker exceptions, and retain fresh declarations across joins.
//!
//! Integration:
//! rules::execution_flow_controller, rules::state_consolidator, rules::joiner,
//! interfaces::verification, verifier pool and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Worker/solver ownership and deferred continuation protocol.
//!
//! Status: partial; solver feasibility, branch selection and concrete worker
//! path/declaration/option transfer are implemented. Parallel task scheduling,
//! cooperative waiting, branch reporting and continuation ownership remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::terms::{Term, TermFactory, UnsupportedSubterms};

/// Source-verifier data captured before the then branch starts, so an offloaded
/// else branch observes the path and solver configuration at the branch point.
#[derive(Clone)]
pub struct BranchTransferSnapshot {
    path_conditions: crate::decider::path_conditions::LayeredPathConditionStack,
    functions: Vec<crate::state::terms::Declaration>,
    macros: Vec<crate::state::terms::Declaration>,
    options: crate::package::Map<String, String>,
    errors_reported: usize,
}

/// Worker state needed to restore its options and collect declarations made
/// during the offloaded branch when the caller is under a join.
pub struct BranchWorkerRestore {
    options: crate::package::Map<String, String>,
    functions_before_branch: Vec<crate::state::terms::Declaration>,
    macro_count_before_branch: usize,
}

#[derive(Debug)]
pub enum BranchTransferError<E> {
    Decider(crate::decider::decider::DeciderError<E>),
    Cleanup {
        primary: crate::decider::decider::DeciderError<E>,
        cleanup: crate::decider::decider::DeciderError<E>,
    },
}

#[derive(Default)]
pub struct BranchJoinDeclarations {
    pub functions: Vec<crate::state::terms::Declaration>,
    pub macros: Vec<crate::state::terms::Declaration>,
}

impl BranchTransferSnapshot {
    pub fn capture<P: crate::interfaces::decider::prover::Prover>(
        decider: &crate::decider::decider::DefaultDecider<P>,
        errors_reported: usize,
    ) -> Self {
        Self {
            path_conditions: decider.pcs.clone(),
            functions: decider.fresh_functions.iter().cloned().collect(),
            macros: decider.fresh_macros.clone(),
            options: decider.options().clone(),
            errors_reported,
        }
    }

    /// Install captured data on a different verifier. Option restoration is
    /// attempted on setup failure and both failures remain observable.
    pub fn install<P: crate::interfaces::decider::prover::Prover>(
        &self,
        worker: &mut crate::decider::decider::DefaultDecider<P>,
        errors_reported: &std::sync::atomic::AtomicUsize,
    ) -> Result<BranchWorkerRestore, BranchTransferError<P::Error>> {
        use std::sync::atomic::Ordering;
        let saved_options = worker.options().clone();
        let setup = (|| {
            worker.reset_options()?;
            worker.set_options(self.options.clone())?;
            worker.declare_fresh_functions(self.functions.iter().cloned())?;
            worker.declare_fresh_macros(self.macros.iter().cloned())?;
            worker.set_path_conditions(self.path_conditions.clone())?;
            errors_reported.store(self.errors_reported, Ordering::SeqCst);
            Ok::<_, crate::decider::decider::DeciderError<P::Error>>(())
        })();
        if let Err(primary) = setup {
            let cleanup = worker
                .reset_options()
                .and_then(|_| worker.set_options(saved_options));
            return Err(match cleanup {
                Ok(()) => BranchTransferError::Decider(primary),
                Err(cleanup) => BranchTransferError::Cleanup { primary, cleanup },
            });
        }
        Ok(BranchWorkerRestore {
            options: saved_options,
            functions_before_branch: worker.fresh_functions.iter().cloned().collect(),
            macro_count_before_branch: worker.fresh_macros.len(),
        })
    }

    /// Restore the caller after it ran another queued task while waiting for
    /// the offloaded branch. `self` is captured after the then branch;
    /// `branch_point` retains the source options from before either branch.
    pub fn restore_after_cooperative_join<P: crate::interfaces::decider::prover::Prover>(
        &self,
        branch_point: &Self,
        decider: &mut crate::decider::decider::DefaultDecider<P>,
        errors_reported: &std::sync::atomic::AtomicUsize,
        saturation: Option<&crate::interfaces::decider::prover::ProverStateSaturationTimeout>,
    ) -> Result<(), crate::decider::decider::DeciderError<P::Error>> {
        use std::sync::atomic::Ordering;
        decider.set_path_conditions(self.path_conditions.clone())?;
        errors_reported.store(self.errors_reported, Ordering::SeqCst);
        if let Some(saturation) = saturation {
            decider
                .prover
                .saturate_configured(Some(saturation))
                .map_err(crate::decider::decider::DeciderError::Prover)?;
        }
        decider.reset_options()?;
        decider.set_options(branch_point.options.clone())
    }
}

impl BranchWorkerRestore {
    /// Restore worker options and return declarations that source transfers
    /// back to the caller after an offloaded branch under a join.
    pub fn finish<P: crate::interfaces::decider::prover::Prover>(
        self,
        worker: &mut crate::decider::decider::DefaultDecider<P>,
        under_join: bool,
    ) -> Result<BranchJoinDeclarations, crate::decider::decider::DeciderError<P::Error>> {
        let declarations = if under_join {
            BranchJoinDeclarations {
                functions: worker
                    .fresh_functions
                    .iter()
                    .filter(|decl| !self.functions_before_branch.contains(decl))
                    .cloned()
                    .collect(),
                macros: worker
                    .fresh_macros
                    .iter()
                    .skip(self.macro_count_before_branch)
                    .cloned()
                    .collect(),
            }
        } else {
            BranchJoinDeclarations::default()
        };
        worker.reset_options()?;
        worker.set_options(self.options)?;
        Ok(declarations)
    }
}

impl BranchJoinDeclarations {
    pub fn declare_on<P: crate::interfaces::decider::prover::Prover>(
        self,
        decider: &mut crate::decider::decider::DefaultDecider<P>,
    ) -> Result<(), crate::decider::decider::DeciderError<P::Error>> {
        decider.declare_fresh_functions(self.functions)?;
        decider.declare_fresh_macros(self.macros)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BranchDecision {
    pub execute_then: bool,
    pub execute_else: bool,
    pub parallelize_else: bool,
    pub skip_feasibility: bool,
}
#[derive(Debug)]
pub enum BranchError<E> {
    Traversal(UnsupportedSubterms),
    Solver(E),
}
/// Compute branch feasibility in source order. Packaging snapshots are not quantified variables.
/// The supplied check is a proof query: true means the proposition is established.
pub fn decide<E>(
    factory: &TermFactory,
    condition: &Term,
    quantified_variables: &[Term],
    short_circuit_and: bool,
    parallelize: bool,
    mut check: impl FnMut(&Term) -> Result<bool, E>,
) -> Result<BranchDecision, BranchError<E>> {
    let negated = factory.not(condition.clone());
    let skip = if short_circuit_and {
        true
    } else if quantified_variables.is_empty() {
        false
    } else {
        let free = condition.free_variables().map_err(BranchError::Traversal)?;
        quantified_variables.iter().any(|var| free.contains(var))
    };
    let execute_then = skip || !check(&negated).map_err(BranchError::Solver)?;
    let execute_else = !execute_then || skip || !check(condition).map_err(BranchError::Solver)?;
    Ok(BranchDecision {
        execute_then,
        execute_else,
        parallelize_else: parallelize && execute_then && execute_else,
        skip_feasibility: skip,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::terms::TermOptions;
    #[test]
    fn infeasible_then_avoids_second_solver_query() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let mut calls = 0;
        let decision = decide(&f, &f.boolean(true), &[], false, true, |_| {
            calls += 1;
            Ok::<_, ()>(true)
        })
        .unwrap();
        assert_eq!(calls, 1);
        assert!(!decision.execute_then && decision.execute_else && !decision.parallelize_else);
    }

    #[test]
    #[ignore = "requires a real Z3 executable in FERRUM_TEST_Z3"]
    fn transfer_replays_source_path_and_returns_join_declarations() {
        use crate::decider::{decider::DefaultDecider, z3_prover_std_io};
        use crate::interfaces::decider::prover::{Prover, TextEmitter};
        use crate::state::identifiers::Identifier;
        use crate::state::terms::{ApplicationTarget, Sort};
        use std::sync::atomic::{AtomicUsize, Ordering};

        let executable = std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let make = |name: &str| {
            DefaultDecider::new(
                z3_prover_std_io::new(
                    name.into(),
                    z3_prover_std_io::settings(executable.clone().into()),
                    factory.clone(),
                    |_| {},
                ),
                false,
                None,
                None,
                None,
            )
        };
        let mut source = make("source");
        let mut worker = make("worker");
        source.start(None).unwrap();
        worker.start(None).unwrap();
        source
            .prover
            .emit("(set-option :print-success true)")
            .unwrap();
        worker
            .prover
            .emit("(set-option :print-success true)")
            .unwrap();
        source
            .set_options(
                [("smt.random_seed".into(), "42".into())]
                    .into_iter()
                    .collect(),
            )
            .unwrap();
        worker
            .set_options(
                [("smt.random_seed".into(), "43".into())]
                    .into_iter()
                    .collect(),
            )
            .unwrap();
        let identity = source.path_condition_identity();
        source.push_scope().unwrap();
        assert!(std::sync::Arc::ptr_eq(
            &identity,
            &source.path_condition_identity()
        ));
        let condition = factory.var(Identifier::new("branchCondition"), Sort::Bool, false);
        let declaration =
            factory.function_decl_target(ApplicationTarget::Variable(condition.clone()));
        source.declare_fresh_functions([declaration]).unwrap();
        let original_macro = factory.macro_decl(
            Identifier::new("branchOriginalMacro"),
            vec![],
            condition.clone(),
        );
        source
            .declare_fresh_macros([original_macro.clone()])
            .unwrap();
        source
            .assume([(condition.clone(), None)], false, false)
            .unwrap();
        let snapshot = BranchTransferSnapshot::capture(&source, 3);
        let errors = AtomicUsize::new(0);
        let worker_identity = worker.path_condition_identity();
        let restore = snapshot.install(&mut worker, &errors).unwrap();
        assert!(!std::sync::Arc::ptr_eq(
            &worker_identity,
            &worker.path_condition_identity()
        ));
        assert_eq!(errors.load(Ordering::SeqCst), 3);
        assert_eq!(
            worker.options().get("smt.random_seed").map(String::as_str),
            Some("42")
        );
        assert!(worker.fresh_macros.contains(&original_macro));
        assert!(worker.prover.assert_goal(&condition, None).unwrap());
        assert!(
            !worker
                .prover
                .assert_goal(&factory.not(condition.clone()), None)
                .unwrap()
        );
        let fresh = factory.var(Identifier::new("branchResult"), Sort::Bool, false);
        let fresh_decl = factory.function_decl_target(ApplicationTarget::Variable(fresh));
        worker
            .declare_fresh_functions([fresh_decl.clone()])
            .unwrap();
        let fresh_macro = factory.macro_decl(
            Identifier::new("branchNewMacro"),
            vec![],
            factory.boolean(true),
        );
        worker.declare_fresh_macros([fresh_macro.clone()]).unwrap();
        let joined = restore.finish(&mut worker, true).unwrap();
        assert_eq!(joined.functions, vec![fresh_decl.clone()]);
        assert_eq!(joined.macros, vec![fresh_macro.clone()]);
        assert_eq!(
            worker.options().get("smt.random_seed").map(String::as_str),
            Some("43")
        );
        joined.declare_on(&mut source).unwrap();
        assert!(source.fresh_functions.contains(&fresh_decl));
        assert!(source.fresh_macros.contains(&fresh_macro));
        let after_then = BranchTransferSnapshot::capture(&source, 5);
        source
            .set_path_conditions(
                crate::decider::path_conditions::LayeredPathConditionStack::new(false),
            )
            .unwrap();
        source
            .assume([(factory.not(condition.clone()), None)], false, false)
            .unwrap();
        errors.store(99, Ordering::SeqCst);
        after_then
            .restore_after_cooperative_join(&snapshot, &mut source, &errors, None)
            .unwrap();
        assert_eq!(errors.load(Ordering::SeqCst), 5);
        assert!(source.prover.assert_goal(&condition, None).unwrap());
        assert_eq!(
            source.options().get("smt.random_seed").map(String::as_str),
            Some("42")
        );
        source.stop().unwrap();
        worker.stop().unwrap();
    }
}
