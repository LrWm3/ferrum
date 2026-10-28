//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/arp/ARPPlugin.scala
//!
//! Purpose:
//! Encode supported abstract read permissions in method contracts, calls and loops.
//!
//! Planned Rust structure:
//! Port ARPPlugin rdPerm, beforeParse/beforeVerify, checkSupported/misplacedRd, rdBounds,
//! replaceRd, rdConstraint, transformBody and FreshNames.
//!
//! Behavior to preserve:
//! The opt-in plugin adds rd keyword and expression parser. Reject occurrences outside methods,
//! inside magic wands or not directly an access-predicate amount before transforming. Add a
//! bounded fresh permission parameter to each method using rd; replace contract/body uses. For
//! calls instantiate callee preconditions and inhale bounds plus conditional current-permission
//! constraints before passing a fresh argument; loops similarly get fresh bounded permissions,
//! rewritten invariants/body and mapped invariant errors. Recurse through conjunction,
//! implication, conditionals, let, forall and exhale side of inhale-exhale, autotriggering
//! untriggered forall. Preserve synthesized metadata, error transformations and fresh-name
//! collision order.
//!
//! Integration:
//! parser::fast_parser; arp AST/PAST extensions, ast::utility::{expressions,rewriter}, verifier
//! errors and frontend plugin ordering.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact permissions, AST metadata, ordering and native plugin
//! registration.
//!
//! Open decisions:
//! Reconcile contextual traversal, generated names and error backtranslation with ast rewriter and
//! verifier.
//!
//! Status: description only; implementation has not started.
