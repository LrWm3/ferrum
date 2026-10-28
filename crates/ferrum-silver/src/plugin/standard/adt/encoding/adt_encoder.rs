//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/adt/encoding/AdtEncoder.scala
//!
//! Purpose:
//! Encode ADTs into Silver domains, functions and axioms before backend verification.
//!
//! Planned Rust structure:
//! Port AdtEncoder encode, tagMapping, constructor/destructor/discriminator conversion, ADT-type
//! conversion and axiom generators for injectivity, tag, exclusivity, contains, transitivity and
//! well-foundedness.
//!
//! Behavior to preserve:
//! Assign constructor tags by sorted name. Bottom-up replace declarations and applications, then
//! rewrite all ADT types, then add contains transitivity domain when derived. Generate
//! constructor/destructor/tag functions and axioms with source triggers; optional well-founded
//! domains require termination enabled, an existing well-founded-order declaration domain and
//! absence of the ADT-specific well-founded domain. Traverse nested ADT
//! constructor types with visited-set guard for decreases axioms; derive contains excluding
//! blocklisted fields and build concrete-type transitive closure. Preserve order, metadata, type
//! maps and actual trigger generation, including exclusivity’s last destructor-call list.
//!
//! Integration:
//! plugin::standard::adt::{adt_plugin,adt_ast_extension,encoding::adt_name_manager};
//! ast domain/type/expression rewriter, termination and ADT resources.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, typed maps, metadata and explicit reconstruction.
//!
//! Open decisions:
//! Reconcile exclusivity trigger accumulation and unordered closure enumeration against upstream
//! tests before any correction.
//!
//! Status: description only; implementation has not started.
