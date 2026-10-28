//! Port plan: Silver types and generic substitution.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Type.scala
//!
//! Purpose:
//! Silver types and generic substitution.
//!
//! Planned Rust structure:
//! Represent Type, BuiltInType/AtomicType and Int, Bool, Perm, Ref, InternalType, Wand; GenericType,
//! CollectionType and SeqType, SetType, MultisetType, MapType; DomainType, TypeVar, BackendType and
//! ExtensionType.
//!
//! Behavior to preserve:
//! Subtyping is equality except Wand <: Bool and same-name DomainType argument-wise subtyping. Preserve
//! concreteness and recursive substitutions; generic argument order comes from typeParameters.
//! DomainType fills missing parameter mappings with the variable itself and substitutes existing
//! mappings rather than overwriting concrete bindings. Keep its parameter-set consistency check and
//! backend interpretations.
//!
//! Integration:
//! Shared by ast::{expression,program,pretty::pretty_printer}, parser type checking,
//! ast::utility::types and Silicon encodings.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Reconcile extension-type representation, structural equality and domain parameter ownership with
//! program and generic substitution utilities.
//!
//! Status: description only; implementation has not started.
