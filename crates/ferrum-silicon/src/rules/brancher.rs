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
//! Status: partial; solver feasibility and parallel-branch selection implemented.
//! Scoped execution, worker transfer, reporting and result joining remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::terms::{Term, TermFactory, UnsupportedSubterms};

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
}
