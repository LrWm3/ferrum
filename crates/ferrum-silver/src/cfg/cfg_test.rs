//! Port plan: Standalone diagnostic driver that prints method CFGs as DOT.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/CfgTest.scala
//!
//! Purpose:
//! Standalone diagnostic driver that prints method CFGs as DOT.
//!
//! Planned Rust structure:
//! Port CfgTest main and private parse helper as an appropriate executable/test utility, without
//! changing its source mapping.
//!
//! Behavior to preserve:
//! Missing filename raises an error; read the file, accept parse results only when all errors are
//! ParseWarning, resolve with false, translate, then print each method name and DOT CFG. Failed
//! optional results are unwrapped upstream.
//!
//! Integration:
//! Uses parser::{fast_parser,resolver,translator}, verifier::ParseWarning, ast::program and
//! cfg::silver.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Decide driver placement and error presentation with parser and eventual CLI; preserve failure
//! distinctions rather than inventing successful fallback.
//!
//! Status: description only; implementation has not started.
