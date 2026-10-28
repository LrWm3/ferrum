//! Ferrum assembly for run-owned symbolic logging, following PLAN.md.
//! Upstream: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Silicon.scala
//! The backend retains the root across verifier resets and closes it after workers stop.
//! Status: partial; explicit ownership and worker attachment are connected.
//! Public configuration, formatter parity and timeout trace reporting remain gated.

use std::{rc::Rc, sync::Arc};

use crate::{
    config::JoinMode,
    interfaces::decider::prover::Prover,
    logger::{
        records::{data::data_record::NativeRecordFactory, symbolic_record::RecordError},
        symb_ex_logger::NativeSymbExLogger,
    },
    verifier::native_context::NativeVerifierContext,
};

/// Backend-owned cleanup authority for a single run root.
pub struct RunLogOwner {
    attachment: RunLogAttachment,
}
/// Cloneable worker attachment; it does not own root shutdown.
#[derive(Clone)]
pub struct RunLogAttachment {
    root: Arc<NativeSymbExLogger>,
    formatter: Option<fn(f64) -> String>,
    trace: bool,
}
impl RunLogOwner {
    /// Trace requires a recording root and an explicitly supplied Java-compatible
    /// double formatter. No formatter leaves Decider statistics inactive.
    pub fn new(
        root: Arc<NativeSymbExLogger>,
        formatter: Option<fn(f64) -> String>,
        trace: bool,
    ) -> Result<Self, RecordError> {
        if trace && !root.supports_trace() {
            return Err(RecordError::Unsupported(
                "trace logger disabled or non-recording",
            ));
        }
        if trace && formatter.is_none() {
            return Err(RecordError::Unsupported(
                "trace double formatter unavailable",
            ));
        }
        Ok(Self {
            attachment: RunLogAttachment {
                root,
                formatter,
                trace,
            },
        })
    }
    pub fn attachment(&self) -> RunLogAttachment {
        self.attachment.clone()
    }
    /// Close after stopping all verifier workers; scheduler close joins its thread.
    pub fn close(&self) -> Result<(), RecordError> {
        self.attachment.root.close()
    }
}
impl RunLogAttachment {
    /// Construct the full-state factory on the context's own thread.
    pub fn attach<S: Prover, P, D>(
        &self,
        context: &mut NativeVerifierContext<S, P, D>,
        factory: Rc<dyn NativeRecordFactory<P, D, JoinMode>>,
    ) {
        context.set_logging_root(Some(self.root.clone()), Some(factory));
        context.set_decider_logging_formatter(self.formatter);
        context.set_trace_reporting_enabled(self.trace);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn traced_owner_requires_recording_and_formatter() {
        use crate::{
            config::Config,
            logger::{log_config::LogConfig, symb_ex_logger::SymbExLog},
            state::terms::{TermFactory, TermOptions},
        };
        let terms = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let disabled = Arc::new(
            NativeSymbExLogger::of_config(
                &Config::default(),
                Arc::new(ferrum_silver::reporter::reporter::NoopReporter),
                terms,
                |_| {},
                |_| {},
            )
            .unwrap(),
        );
        assert!(RunLogOwner::new(disabled.clone(), Some(|n| n.to_string()), true).is_err());
        assert!(RunLogOwner::new(disabled, None, false).is_ok());
        let enabled = Arc::new(NativeSymbExLogger::Enabled(SymbExLog::new(
            LogConfig::default(),
        )));
        assert!(RunLogOwner::new(enabled.clone(), None, true).is_err());
        let owner = RunLogOwner::new(enabled, Some(|n| n.to_string()), true).unwrap();
        let _attachment = owner.attachment();
        owner.close().unwrap();
    }
    #[test]
    fn attachment_can_cross_worker_threads() {
        fn require_send_sync<T: Send + Sync>() {}
        require_send_sync::<RunLogAttachment>();
    }
}
