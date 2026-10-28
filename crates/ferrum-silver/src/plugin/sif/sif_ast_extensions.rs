//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/sif/SIFAstExtensions.scala
//!
//! Purpose:
//! Define relational expressions and frontend control-flow extensions used by the SIF product
//! transformation.
//!
//! Planned Rust structure:
//! Port SIFLowExp, SIFLowEventExp, SIFRelExp, SIFLowExitExp and SIFTerminatesExp;
//! return/break/continue/raise, exception handler/try-catch, declassify, inlined-call and
//! assert-no-exception statements; SIFInfo and SIFDynCheckInfo.
//!
//! Behavior to preserve:
//! Preserve expression types and purity, optional low comparator/type map, execution index and all
//! subnodes/metadata. Control-flow extensions beyond low/rel have no parser in SIFPlugin. Direct
//! verification of relational expression extensions is unimplemented and requires transformation.
//! Preserve try-catch subnode traversal as written.
//!
//! Integration:
//! sif_plugin, sifp_ast_extensions and sif_extended_transformer; ast::{expression,statement,ast} metadata and pretty printer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for metadata, node identity and extension dispatch.
//!
//! Open decisions:
//! Agree on frontend-created extension ownership, comparator signatures and direct-verification
//! failure with AST and verifier.
//!
//! Status: description only; implementation has not started.
