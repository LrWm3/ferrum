//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/sif/SIFError.scala
//!
//! Purpose:
//! Define information-flow check failures and reasons.
//!
//! Planned Rust structure:
//! Port SIFTerminationChannelCheckFailed, SIFGotoCheckFailed and fold, unfold,
//! termination-condition and goto reason variants.
//!
//! Behavior to preserve:
//! Preserve IDs, texts, offending node types and reason transformations. Error withNode/withReason
//! constructors omit cached flag and thereby reset it to false; preserve as an observed issue for
//! reconciliation.
//!
//! Integration:
//! sif_extended_transformer attaches errors and reasons; verifier error interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for diagnostics, metadata and error transformations.
//!
//! Open decisions:
//! Reconcile cached-flag behavior and typed error-node replacement with verifier.
//!
//! Status: description only; implementation has not started.
