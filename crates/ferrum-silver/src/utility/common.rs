//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/Common.scala
//!
//! Purpose:
//! Provide structural equality, file writing and exact rational arithmetic.
//!
//! Planned Rust structure:
//! Port StructuralEquality and generateHashCode, toFile/PrintWriter, Rational and zero/one
//! constructors.
//!
//! Behavior to preserve:
//! Equality checks runtime type and defining members; hash folds by 41. Rational rejects zero
//! denominator, normalizes by gcd with positive denominator, and supports exact
//! arithmetic/comparison. Upstream hash uses original n,d despite normalized equality: preserve
//! or document a deliberate fix. File writer creates parents and supports append/autoflush.
//!
//! Integration:
//! Shared by Silver and downstream utility clients; rational consumers must agree on arithmetic.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Resolve Rational hash/equality mismatch and runtime-specific hash compatibility with
//! consumers.
//!
//! Status: description only; implementation has not started.
