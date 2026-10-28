//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/refute/RefuteErrors.scala
//!
//! Purpose:
//! Define failures for refutations that could not be shown false.
//!
//! Planned Rust structure:
//! Represent RefuteError, RefuteErrorReason, RefuteFailed and RefutationTrue with IDs, positions,
//! node/reason replacement and cached flag.
//!
//! Behavior to preserve:
//! RefuteFailed uses expression position and special smoke message for false with
//! SmokeDetectionInfo; otherwise it reports that assertion holds or was unreachable. Preserve
//! upstream withNode behavior, which ignores its replacement argument, as an open issue.
//!
//! Integration:
//! refute_plugin creates these errors; smoke::smoke_detection_plugin supplies metadata; verifier
//! errors and reasons.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for diagnostics and error transformations.
//!
//! Open decisions:
//! Reconcile the apparent withNode bug with verifier error contracts before deciding whether to
//! correct it.
//!
//! Status: description only; implementation has not started.
