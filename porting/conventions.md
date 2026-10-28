# Shared port conventions

These rules support the description stage in [PLAN.md](../PLAN.md). They describe
semantic requirements and provisional design choices, not implemented APIs.

## Settled requirements

- Preserve the pinned Silver/Silicon behavior, rule order, configuration branches,
  diagnostics, and failure propagation. Record suspected upstream bugs explicitly;
  do not silently correct or blindly reproduce them when the intended behavior is
  uncertain. Resolve them against callers and the later differential test pass.
- Keep one upstream source per initial Rust destination. Module comments own the
  local symbol outline; `modules.toml` owns mappings and reviewed stage status.
  `sources.toml` owns revisions. `non_rust_files.tsv` inventories other tracked
  paths with provisional dispositions; this does not mean those assets are ported.
- The current Rust files contain only `//!` comments. A complete description is
  neither a compiled interface nor a correctness result. Do not add executable
  placeholders or count a missing verification rule as success.
- Preserve distinctions between structural equality, reference identity, fresh
  identifiers, and hash-consed terms. Keep equality and hashing contracts visible.
- Preserve observable collection order, including deterministic fresh names,
  declaration emission, trigger order, traversal, and error reporting. Do not
  substitute unordered collections solely because both APIs say map or set.
- Branch state copies must preserve the upstream separation of mutable state.
  Shared immutable data can be shared; solver scopes, logging state, caches, and
  mutable records require explicit ownership and restoration boundaries.
- Preserve exact integer/rational arithmetic and distinctions among missing,
  invalid, unsupported, timeout, unknown, unreachable, and successful results.
- Keep the crate dependency direction `ferrum -> ferrum-silicon -> ferrum-silver`,
  with the facade also using Silver. Silver must not depend on Silicon.

## Open representation choices

- **AST handles and metadata:** owned enums, reference-counted nodes, or arenas
  remain proposals. Reconcile traversal, rewriting, parent links, source metadata,
  cached properties, and identity-sensitive callers before choosing one globally.
- **Terms and snapshots:** enum/newtype layouts and interning policy remain open.
  Read factory normalization and equality rules before deciding which values can
  share identity. A Rust heap snapshot is a symbolic verifier value, not permission
  to change the encoded ownership or permission semantics.
- **State and contexts:** distinguish logically copied branch state from the
  verifier's services. Explicit context parameters are the default outline;
  exact borrowing, sharing, worker ownership, and mutable-cache policy are open.
- **Continuations:** producer, consumer, evaluator, executor, brancher, and joiner
  must agree on control flow and verifier/state handoff. Closures, explicit frames,
  or another encoding can be chosen later; a simple `Result` is not automatically
  equivalent to the upstream continuation protocol.
- **Collections:** ordered maps/sets and persistent collections may need wrappers.
  Concrete crates are not selected during the description stage.
- **Errors and lifecycle:** preserve the existing public/backend result boundary
  and lifecycle transitions. Exact Rust error enums, cancellation, cleanup and
  timeout APIs must be reconciled with frontend and solver owners.
- **Solver processes:** preserve request/response order and scope balance.
  Process transport, interruption, locking and per-worker reuse are open; shared
  access must not mix independent solver sessions.
- **Parser and plugins:** keep grammar, precedence, extension points and plugin
  order. Rust parser technology and native plugin registration are open choices.
- **JVM replacements:** reflection, Scala macros, process management and logging
  need native mechanisms. Describe the required behavior before selecting one.

## Review and progress

Agents read the pinned source and its immediate collaborators, write file-specific
briefs, and report unresolved cross-file decisions. The coordinator checks source
links, comment-only contents, coverage and representative behavioral claims,
reconciles shared issues, and advances reviewed entries to `described` in logical
commits. Structural validation cannot prove the accuracy or completeness of prose.

Source-specific open issues stay in their module comments. Promote an issue here
when it needs agreement across components; record adopted behavior changes in
`differences.md` once a decision is made.
