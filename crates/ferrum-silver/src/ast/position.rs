//! Port plan: Source, virtual and frontend identifier locations used in diagnostics.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Position.scala
//!
//! Purpose:
//! Source, virtual and frontend identifier locations used in diagnostics.
//!
//! Planned Rust structure:
//! Represent Position, NoPosition, HasLineColumn/HasIdentifier, LineColumnPosition,
//! AbstractSourcePosition, SourcePosition, IdentifierPosition, TranslatedPosition, FilePosition,
//! VirtualPosition and LineCol parser adapter.
//!
//! Behavior to preserve:
//! Keep line/column ordering and deltaColumn semantics, optional end positions, basename-based
//! rendering, identifier-specific equality, and parser index-to-line/column conversion. Preserve source
//! subclasses and virtual identifiers rather than collapsing them to a single span.
//!
//! Integration:
//! Used by ast metadata and verifier diagnostics; LineCol cooperates with parser::fast_parser and
//! source paths.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Agree on path and identifier equality, parser offset conventions and translated-position
//! representation with parser and verifier.
//!
//! Status: description only; implementation has not started.
