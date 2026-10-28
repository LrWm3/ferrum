//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/DataRecord.scala
//!
//! Purpose:
//! Attach source node and path conditions to symbolic data records.
//!
//! Planned Rust structure:
//! Port DataRecord value, pcs, string rendering and getData.
//!
//! Behavior to preserve:
//! Render null value as null; populate source position for Positioned nodes and include captured
//! ordered assumptions only if includePcs enabled.
//!
//! Integration:
//! logger::records::symbolic_record/record_data and concrete data records; Silver positions and
//! state.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for optional data and immutable state capture.
//!
//! Open decisions:
//! Agree on source position serialization and path condition ownership with writer.
//!
//! Status: node and path-condition capture implemented; source-compatible rendering is injected.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::{
    common::collections::immutable::insertion_ordered_set::InsertionOrderedSet,
    logger::{
        log_config::LogConfig,
        records::{
            record_data::RecordData,
            symbolic_record::{RecordError, RecordRenderer, SymbolicRecord},
        },
    },
    state::terms::Term,
};
use ferrum_silver::ast::utility::nodes::Node;
pub trait DataRecord: SymbolicRecord {
    fn value(&self) -> Option<Node>;
    fn pcs(&self) -> Option<&InsertionOrderedSet<Term>>;
}
pub fn data_for(
    record: &dyn DataRecord,
    config: &LogConfig,
    renderer: &dyn RecordRenderer,
) -> Result<RecordData, RecordError> {
    let pos = record
        .value()
        .map(|node| renderer.source_line_column(&node))
        .transpose()?;
    Ok(RecordData {
        pos,
        pcs: if config.include_pcs {
            record.pcs().cloned()
        } else {
            None
        },
        ..RecordData::default()
    })
}

/// Owner-local adapter for constructing source records without imposing Send or
/// Sync bounds on every verifier context. Implementations decide which concrete
/// state types can be retained by cross-thread symbolic records.
pub trait NativeRecordFactory<P, D, J> {
    fn evaluate(
        &self,
        expression: &ferrum_silver::ast::expression::Exp,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord>;
    fn produce(
        &self,
        assertion: &ferrum_silver::ast::expression::Exp,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord>;
    fn consume(
        &self,
        assertion: &ferrum_silver::ast::expression::Exp,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord>;
    fn method_call(
        &self,
        statement: &ferrum_silver::ast::statement::Stmt,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord>;
    fn execute(
        &self,
        statement: &ferrum_silver::ast::statement::Stmt,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord>;
    fn comment(
        &self,
        comment: &str,
        state: Option<&crate::state::state::State<P, D, J>>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord>;
    fn wellformedness(
        &self,
        posts: &[ferrum_silver::ast::expression::Exp],
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord>;
    fn conditional_edge(
        &self,
        expression: &ferrum_silver::ast::expression::Exp,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord>;
    fn joining(
        &self,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord>;
    fn implies(
        &self,
        expression: Option<&ferrum_silver::ast::expression::Exp>,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
        env: &str,
    ) -> std::sync::Arc<dyn DataRecord>;
    fn conditional_expression(
        &self,
        expression: &ferrum_silver::ast::expression::Exp,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
        env: &str,
    ) -> std::sync::Arc<dyn DataRecord>;
}

/// Retain the complete persistent state and a snapshot of current assumptions,
/// exactly as the source data-record constructors do.
#[derive(Clone, Copy, Debug, Default)]
pub struct FullStateRecordFactory;
impl<P, D, J: Clone> NativeRecordFactory<P, D, J> for FullStateRecordFactory
where
    crate::state::state::State<P, D, J>: Send + Sync + 'static,
{
    fn evaluate(
        &self,
        expression: &ferrum_silver::ast::expression::Exp,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord> {
        std::sync::Arc::new(super::evaluate_record::EvaluateRecord::new(
            Some(expression.clone()),
            Some(state.clone()),
            Some(paths),
        ))
    }
    fn produce(
        &self,
        assertion: &ferrum_silver::ast::expression::Exp,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord> {
        std::sync::Arc::new(super::produce_record::ProduceRecord::new(
            Some(assertion.clone()),
            Some(state.clone()),
            Some(paths),
        ))
    }
    fn consume(
        &self,
        assertion: &ferrum_silver::ast::expression::Exp,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord> {
        std::sync::Arc::new(super::consume_record::ConsumeRecord::new(
            Some(assertion.clone()),
            Some(state.clone()),
            Some(paths),
        ))
    }
    fn method_call(
        &self,
        statement: &ferrum_silver::ast::statement::Stmt,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord> {
        std::sync::Arc::new(super::method_call_record::MethodCallRecord::new(
            Some(statement.clone()),
            Some(state.clone()),
            Some(paths),
        ))
    }
    fn execute(
        &self,
        statement: &ferrum_silver::ast::statement::Stmt,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord> {
        std::sync::Arc::new(super::execute_record::ExecuteRecord::new(
            Some(statement.clone()),
            Some(state.clone()),
            Some(paths),
        ))
    }
    fn comment(
        &self,
        comment: &str,
        state: Option<&crate::state::state::State<P, D, J>>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord> {
        std::sync::Arc::new(super::comment_record::CommentRecord::new(
            Some(comment.to_owned()),
            state.cloned(),
            Some(paths),
        ))
    }
    fn wellformedness(
        &self,
        posts: &[ferrum_silver::ast::expression::Exp],
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord> {
        std::sync::Arc::new(
            super::wellformedness_check_record::WellformednessCheckRecord::new(
                posts.to_vec(),
                Some(state.clone()),
                Some(paths),
            ),
        )
    }
    fn conditional_edge(
        &self,
        expression: &ferrum_silver::ast::expression::Exp,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord> {
        std::sync::Arc::new(super::conditional_edge_record::ConditionalEdgeRecord::new(
            Some(expression.clone()),
            Some(state.clone()),
            Some(paths),
        ))
    }
    fn joining(
        &self,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
    ) -> std::sync::Arc<dyn DataRecord> {
        std::sync::Arc::new(
            crate::logger::records::structural::joining_record::JoiningRecord::new(
                Some(state.clone()),
                Some(paths),
            ),
        )
    }
    fn implies(
        &self,
        expression: Option<&ferrum_silver::ast::expression::Exp>,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
        env: &str,
    ) -> std::sync::Arc<dyn DataRecord> {
        std::sync::Arc::new(super::implies_record::ImpliesRecord::new(
            expression.cloned(),
            Some(state.clone()),
            Some(paths),
            env.to_owned(),
        ))
    }
    fn conditional_expression(
        &self,
        expression: &ferrum_silver::ast::expression::Exp,
        state: &crate::state::state::State<P, D, J>,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
        env: &str,
    ) -> std::sync::Arc<dyn DataRecord> {
        std::sync::Arc::new(super::cond_exp_record::CondExpRecord::new(
            Some(expression.clone()),
            Some(state.clone()),
            Some(paths),
            env.to_owned(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        config::JoinMode,
        decider::path_conditions::LayeredPathConditionStack,
        state::{
            identifiers::Identifier,
            terms::{Sort, TermFactory, TermOptions},
        },
        verifier::verification_pool_manager::NativeBranchState,
    };
    use ferrum_silver::ast::{
        expression::{Exp, ExpKind},
        program::Program,
    };

    #[test]
    fn native_factory_retains_state_and_snapshots_assumptions() {
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
        let mut state = NativeBranchState::new(
            program,
            Default::default(),
            Default::default(),
            JoinMode::All,
            &factory,
            false,
            false,
        );
        state.under_join = true;
        let expression = Exp::new(ExpKind::TrueLit, Default::default());
        let assumption = factory.var(Identifier::new("p"), Sort::Bool, false);
        let mut paths = LayeredPathConditionStack::new(false);
        paths.add(&assumption).unwrap();
        let producer = FullStateRecordFactory;
        let records = [
            producer.evaluate(&expression, &state, &paths),
            producer.produce(&expression, &state, &paths),
            producer.consume(&expression, &state, &paths),
            producer.joining(&state, &paths),
            producer.implies(None, &state, &paths, "ForPerm"),
            producer.conditional_expression(&expression, &state, &paths, "CondExp"),
        ];
        state.under_join = false;
        paths
            .add(&factory.var(Identifier::new("q"), Sort::Bool, false))
            .unwrap();
        for record in &records {
            assert_eq!(record.pcs().unwrap().len(), 1);
            assert!(record.pcs().unwrap().contains(&assumption));
        }
        let captured = records[0]
            .as_any()
            .downcast_ref::<super::super::evaluate_record::EvaluateRecord<NativeBranchState>>()
            .unwrap();
        assert!(captured.state.as_ref().unwrap().under_join);
        assert!(captured.value.as_ref().unwrap().same_node(&expression));
        assert!(
            records[1]
                .as_any()
                .downcast_ref::<super::super::produce_record::ProduceRecord<NativeBranchState>>()
                .unwrap()
                .state
                .is_some()
        );
        assert!(
            records[2]
                .as_any()
                .downcast_ref::<super::super::consume_record::ConsumeRecord<NativeBranchState>>()
                .unwrap()
                .state
                .is_some()
        );
        let joining = records[3].as_any().downcast_ref::<crate::logger::records::structural::joining_record::JoiningRecord<NativeBranchState>>().unwrap();
        assert!(joining.state.as_ref().unwrap().under_join);
        let implies = records[4]
            .as_any()
            .downcast_ref::<super::super::implies_record::ImpliesRecord<NativeBranchState>>()
            .unwrap();
        assert!(implies.value.is_none());
        assert_eq!(implies.env, "ForPerm");
        let conditional = records[5]
            .as_any()
            .downcast_ref::<super::super::cond_exp_record::CondExpRecord<NativeBranchState>>()
            .unwrap();
        assert!(conditional.value.as_ref().unwrap().same_node(&expression));
        assert_eq!(conditional.env, "CondExp");
    }
}
