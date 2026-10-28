//! Ferrum assembly for the source ExecutionTraceReport, following PLAN.md.
//! Upstream: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/DefaultMainVerifier.scala
//! The caller supplies the actual domain and postcondition axioms in source order.
//! Status: partial; lazy report assembly is connected. Top-level collection and
//! public profile activation require additional runtime integration.

use crate::{
    logger::{
        records::symbolic_record::RecordError,
        renderer::{renderer::Renderer, simple_tree_renderer::SimpleTreeRenderer},
        state_reporting::NativeStateRecordRenderer,
        symb_ex_logger::{MemberSymbExLog, NativeSymbExLogger},
    },
    state::terms::{Term, TermFactory},
};
use ferrum_silver::reporter::message::{Message, TraceValue};
use std::{fmt, sync::Arc};

struct MemberTrace {
    log: Arc<MemberSymbExLog>,
    factory: TermFactory,
}
impl fmt::Debug for MemberTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("MemberTrace(..)")
    }
}
impl fmt::Display for MemberTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let records = self.log.records().map_err(|_| fmt::Error)?;
        let renderer = NativeStateRecordRenderer {
            factory: &self.factory,
        };
        let tree = SimpleTreeRenderer {
            text: &renderer,
            factory: &self.factory,
        }
        .render_member(&records)
        .map_err(|_| fmt::Error)?;
        f.write_str(&tree)
    }
}
#[derive(Debug)]
struct TermTrace(Term);
impl fmt::Display for TermTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let value = crate::reporting::formatters::render_term(&self.0).map_err(|_| fmt::Error)?;
        f.write_str(&value)
    }
}

/// Capture the ordered member handles and actual axiom terms. Member contents are rendered
/// when the receiving reporter renders the message, matching the source's `toString` timing.
pub fn execution_trace_report(
    logger: &NativeSymbExLogger,
    factory: &TermFactory,
    axioms: Vec<Term>,
    function_post_axioms: Vec<Term>,
) -> Result<Message, RecordError> {
    let member_traces = logger
        .logs()?
        .into_iter()
        .map(|log| {
            Arc::new(MemberTrace {
                log,
                factory: factory.clone(),
            }) as Arc<dyn TraceValue>
        })
        .collect();
    let terms = |values: Vec<Term>| {
        values
            .into_iter()
            .map(|term| Arc::new(TermTrace(term)) as Arc<dyn TraceValue>)
            .collect()
    };
    Ok(Message::ExecutionTrace {
        member_traces,
        axioms: terms(axioms),
        function_post_axioms: terms(function_post_axioms),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        decider::path_conditions::LayeredPathConditionStack,
        logger::{
            log_config::LogConfig, records::data::comment_record::CommentRecord,
            symb_ex_logger::SymbExLog,
        },
        state::terms::TermOptions,
    };
    use ferrum_silver::{
        ast::program::{Member, Predicate, PredicateData},
        reporter::reporter::{NoopReporter, PollingReporter, Reporter},
    };

    #[test]
    fn report_uses_ordered_live_member_logs_and_actual_axioms() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let logger = NativeSymbExLogger::Enabled(SymbExLog::new(LogConfig::default()));
        let renderer = NativeStateRecordRenderer { factory: &factory };
        let paths = LayeredPathConditionStack::new(false);
        let member = |name: &str| {
            Member::Predicate(Predicate::new(PredicateData {
                name: name.into(),
                formal_args: vec![],
                body: None,
                meta: Default::default(),
            }))
        };
        let first = logger
            .open_member_scope(member("first"), &paths, &renderer)
            .unwrap();
        logger
            .open_member_scope(member("second"), &paths, &renderer)
            .unwrap();
        let message = execution_trace_report(
            &logger,
            &factory,
            vec![factory.int_literal(7)],
            vec![factory.boolean(true)],
        )
        .unwrap();
        let reporter = PollingReporter::new(Arc::new(NoopReporter));
        reporter.report(message).unwrap();
        let scope = first
            .open_scope(
                Arc::new(CommentRecord::<()>::new(Some("late".into()), None, None)),
                &renderer,
            )
            .unwrap();
        first.close_scope(scope).unwrap();
        let report = reporter.get_new_message().unwrap().render_source().unwrap();
        let first_pos = report.find("predicate first").unwrap();
        let late_pos = report.find("comment late").unwrap();
        let second_pos = report.find("predicate second").unwrap();
        assert!(first_pos < late_pos && late_pos < second_pos);
        assert!(report.contains("axioms=List(7)"));
        assert!(report.contains("functionPostAxioms=List(True)"));
    }
}
