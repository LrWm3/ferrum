//! Port plan: Construct interpreted bitvector and floating-point Silver domains.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/BackendTypeFactories.scala
//!
//! Purpose:
//! Construct interpreted bitvector and floating-point Silver domains.
//!
//! Planned Rust structure:
//! BVFactory, RoundingMode (RNE, RNA, RTP, RTN, RTZ), FloatFactory and their type, domain and
//! BackendFunc factories.
//!
//! Behavior to preserve:
//! Preserve names, Boogie and SMTLIB interpretation strings, argument and return types,
//! operation names, bit widths and rounding modes. BV includes logical/arithmetic shifts,
//! signed and unsigned remainder and conversions; Float includes arithmetic, comparisons,
//! predicates and bitvector conversions. Function factory passes the supplied function name as
//! domain name: reconcile this source detail before changing it.
//!
//! Integration:
//! ast::{program,type,expression}; backend interpretation consumers in Silicon.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Agree on interpretation validation and the function/domain-name convention with backend
//! encoding.
//!
//! Status: description only; implementation has not started.
