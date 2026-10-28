//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/ProgramSubmitter.scala
//!
//! Purpose:
//! Optionally submit program and verification metrics to the upstream collection service.
//!
//! Planned Rust structure:
//! Port ProgramSubmitter, ManualProgramSubmitter, FEProgramSubmitter, FileProgramSubmitter and
//! ViperProgramSubmitter; retain setters, formatting and runtime calculation.
//!
//! Behavior to preserve:
//! Submit only when enabled and host nonempty; send program, frontend, args, verifier, success
//! and runtime; catch submission failure. Frontend args filter submission flag and .vpr
//! filenames; file reading failures yield empty text; only Success counts as success.
//!
//! Integration:
//! frontend::sil_frontend, ast::pretty::pretty_printer and verifier::verification_result.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Choose native HTTP/configuration and source ownership with frontend; preserve opt-in behavior.
//!
//! Status: description only; implementation has not started.
