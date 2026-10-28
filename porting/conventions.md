# Shared port conventions

These rules support the implementation sequence in [PLAN.md](../PLAN.md). They
distinguish semantic requirements, adopted interfaces and open design choices.

## Settled requirements

- Preserve the pinned Silver/Silicon behavior, rule order, configuration branches,
  diagnostics, and failure propagation. Record suspected upstream bugs explicitly;
  do not silently correct or blindly reproduce them when the intended behavior is
  uncertain. Resolve them against callers and the later differential test pass.
- Keep one upstream source per initial Rust destination. Module comments own the
  local symbol outline; `modules.toml` owns mappings and reviewed stage status.
  `sources.toml` owns revisions. `non_rust_files.tsv` inventories other tracked
  paths with provisional dispositions; this does not mean those assets are ported.
- Files still marked `described` contain only `//!` comments. `skeleton` means
  implementation is partial, with gaps recorded in the inventory and source.
  A compiled interface is not a correctness result. Incomplete executable entry
  points must explicitly fail; never count a missing verification rule as success.
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

## Adopted implementation boundaries

- Rust 1.89.0, edition 2024, three packages and a committed lockfile are the
  reproducible build baseline. Module declarations activate the tree without
  claiming the described modules are implemented.
- Verification expressions and statements use typed, immutable `Arc` handles;
  metadata stays outside structural equality, and pointer identity is available
  separately for identity-sensitive rewriting. Lazy caches are explicit state.
- The mutable parser graph uses typed `Arc<RwLock<_>>` handles and weak navigation
  links. This permits `SourcePNodeInfo` to retain real parser nodes in worker-safe
  metadata. Release guards before recursive traversal or callbacks; do not use
  unsafe `Send` or discard source metadata to bypass ownership constraints.
- Term construction receives explicit options. Flyweight terms use a shared,
  process-wide strong pool, preserving reuse across verifier contexts. Each term
  keeps a stable equality mode; reject mixing modes in one graph. Recursive
  construction happens before locking the pool. Nonflyweight equality is structural.
- Bundled resources are copied unchanged from pinned `src/main/resources` trees,
  embedded in each crate and covered by SHA-256 entries in `resources.toml`.
  Preamble reading accepts a resource provider; missing resources are errors.
  Native resources replace JVM classpath lookup. Java archive URL behavior stays
  explicitly unsupported until a native caller contract is reconciled.
- Exact arithmetic uses the pinned num crates; insertion-ordered containers use
  indexmap. This does not authorize unordered replacements elsewhere.

## Remaining representation choices

- **AST handles and metadata:** owned enums, reference-counted nodes, or arenas
  remain choices for other node families. Reconcile traversal, rewriting, parent links, source metadata,
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
  Use the selected indexmap where its semantics match; persistent structures may
  need additional adapters.
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
