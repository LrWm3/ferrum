# Differences from upstream

Implementation has begun. Unresolved upstream issues remain proposals in source
comments; the following changes are adopted explicitly.

## Dominator label update

Silver `cfg/utility/Dominators.scala` evaluates `label(index) == ancestorLabel`
where path compression requires assigning the ancestor's better label. The
source-compatible translation was committed separately before this correction.

For blocks 0 through 3, entry 0, and edges in order
`0->1, 0->2, 1->2, 1->3, 2->3`, upstream behavior gives immediate dominator 1
for block 3. Path `0->2->3` avoids block 1, so only block 0 can immediately
dominate block 3. A temporary independent iterative-dominator implementation
and the compiled source-compatible Rust port confirmed the mismatch.

Ferrum assigns the better label during compression. The four-block regression
checks the correct result, guarding a graph relation needed by loop detection.
This is an explicit correctness fix, not a claim that every CFG algorithm has
been broadly validated.

## CFG block iteration

Silver `cfg/silver/CfgGenerator.scala` emits its Phase 2 block list from a
Scala mutable HashMap. Ferrum currently emits values from Rust's HashMap;
neither API specifies statement or insertion order, and Rust iteration can
vary across runs. Edges retain their source construction order. This does
not reproduce Scala's incidental hash-table layout. CFG listing order and
any downstream solver-emission effects need attention in differential and
performance testing; no blanket sorting policy is applied.

Loop augmentation also retains an explicit error for upstream's invalid
`Kind.asInstanceOf` branch when an edge enters multiple loop boundaries.
This is a translated failure path, not a completed correction. The separate
AST loop-info projection overload remains unimplemented.

## Canonical rational hashing

Silver `utility/Common.scala` compares normalized rational values but hashes its
original numerator/denominator arguments. Ferrum hashes the reduced representation,
so equal fractions satisfy Rust's `Eq`/`Hash` contract. Exact arithmetic, ordering
and displayed reduced fractions remain unchanged. Native hash values are not a
cross-runtime serialization format. Focused equivalent-fraction hash checks pass;
term interning and cache behavior remain part of later integration validation.

## Explicit native I/O failures

Silver `Common.PrintWriter` uses Java's error-suppressing writer. The Rust adapter
returns `io::Result` for writes and flushes rather than silently suppressing errors.
Callers must propagate or explicitly report these errors. Parent-directory creation,
append/truncate behavior and explicit line auto-flush are retained.

## Stable term equality mode

Silicon's term equality consults the global flyweight configuration. Rust terms
will retain the mode chosen at construction, with process-wide strong flyweight
pooling and structural nonflyweight equality. Mixing modes in one graph is rejected
to preserve a stable, symmetric `Eq`/`Hash` contract. Configuration remains explicit;
this does not normalize formulas or change solver encodings. Focused tests cover
singleton identity, declaration equivalence and mixed-mode rejection. Full term/cache and solver integration checks remain.

## Chunk context and rendering boundaries

Silicon `state/Chunks.scala` obtains the debug flag from global configuration
when constructing quantified field chunks, including copies. The current Rust
chunk captures that flag explicitly, excludes it from structural equality and
retains it during copy operations. Reconstructing with a changed context remains
possible through its constructor. The configuration/lifecycle port must reconcile
callers that change debugging mode between construction and copying before this
boundary can be considered equivalent.

Basic mask resources use the known field, predicate and wand `ResourceKey`
variants in place of Scala's `Any`. Supporting other extension resources requires
an explicit typed variant or extension contract.

Heap `equalChunks` currently accepts a source-rendering adapter because complete
term/chunk formatting is not ported. It preserves stable sorting by Java UTF-16
string order, including ties, then compares chunks. Supplying Rust Debug output
would not establish source compatibility; default rendering remains a tracked gap.

## Native solver process boundary

The stdio adapter owns one Unix solver process and merges stdout and stderr into
one native stream. RAII cleanup replaces JVM shutdown hooks. Query failures attempt
to pop their temporary assertion scope before propagating the original error;
model-read I/O errors propagate instead of printing an exception and returning an
empty model string. Stop attempts all cleanup even when a flush fails. Non-Unix
process creation remains unsupported until a merged-stream adapter is supplied.

Solver profiles and settings are explicit constructor inputs; configuration and
reporter adapters remain to be connected. SMT output uses equivalent token syntax
without reproducing the source pretty-printer's line wrapping. Empty-binder
quantifiers retain the source warning-and-body behavior with a typed warning;
exact diagnostic term formatting remains a gap. Assertion timing comments use
elapsed milliseconds rather than the source's localized duration formatter.

A native Z3 4.16.0 probe exercised both assertion modes, successful and failed
proofs, model parsing, push/pop, satisfiability and statistics. This validates a
solver round trip, not the unassembled verification engine or all SMT encodings.

## Native resource loading

Pinned text resources are embedded byte-for-byte; no Java classloader is required.
Preamble lookup uses an injectable native resource provider. General `jar:` and
`resource:` URL-to-filesystem conversion in Silver Paths remains an explicit port
gap, not an equivalent implementation. File URLs and ordinary path helpers retain
their implemented native behavior. Resource bytes are checked against pinned Git
objects; full parser/frontend resource integration is still pending.

When adopting a deviation, record its pinned source location, upstream behavior,
Rust behavior, reason, affected callers, and validation plan here. Moving files,
changing representations, or replacing JVM mechanisms does not itself establish
that behavior is equivalent.

## Native ordering, counters and rendering boundaries

Rust hash collections and heap ties do not reproduce Scala's incidental map or
priority-queue order. Chopper equal-penalty cuts and quantified-permission tag
selection need differential review. Ordered source collections retain explicit
insertion order. Base-verifier counters use equality within a concrete Rust key
type; Scala AnyRef keys can compare across runtime classes.

Inverse-function name generation serializes the complete counter operation to
avoid concurrent duplicate names. The source zero-variable field case still does
not advance the counter. Method scoped declarations are computed through fallible
native traversal rather than the source's eager cached field.

Source AST reconstruction retains Scala's structural-equality behavior: an
unforced parent copy can discard equal-syntax child metadata changes. The new
bottom-up forced-copy traversal is used where extra return-type changes must be
preserved; it does not silently change the existing preorder reconstruction rule.

Complete source printers remain explicit dependencies where required. Native
Debug strings are not accepted as equivalent AST/term rendering. Silver cache
hashes preserve MD5 and the unusual decoded-binary-digest string, including Java's
UTF-8 replacement handling; source class names, full pretty printing and other
platform charsets still require adapters.

## Native recorder ownership

Recorder construction uses explicit typed factories instead of JVM reflection.
Source providers and registry ownership are local-thread handles. File operations
return native I/O errors and stop attempts all registered flushes, retaining the
first error. Symbolic log records share identity across branch trees; source
rendering and floating-point text conversion remain explicit boundaries. Progress
reporting currently exposes ordered polling and scope/branch hooks; a native
fixed-delay scheduler and automatic hook registration remain to be connected.

## Counterexample reconstruction that cannot advance

Silicon's set and multiset reconstruction can loop indefinitely when model
operations refer to operands that are never seeded. Ferrum returns the explicit
`NoProgress` error after a pass that resolves no pending operation. This changes
an upstream nontermination case into a diagnostic; it does not fabricate a model.
Model map/set iteration does not reproduce Scala's incidental order. Non-ASCII
predicate name comparisons and unavailable source printers remain explicit
unsupported paths instead of approximated output.

## Native API and debugger boundaries

The Z3 API conversion/session port uses typed native context and driver contracts;
no concrete linked Z3 binding is selected yet. Assertion handling proves a goal
only on UNSAT and attempts scope restoration on error. It is not an alias for the
working stdio transport and does not establish native API parity.

Debug tokens retain the source ASCII grammar. `debug@` is lexically accepted
upstream but its split-index construction fails; native construction reports a
specific error. Debugger input/worker/solver services propagate typed failures;
the interactive loop, complete printing and failure-context assembly are pending.
The dormant flyweight annotation has an explicit native pool rather than a new
procedural macro. Concurrent creation returns the canonical stored handle.


## Native execution assembly

The first concrete runtime composes the translated rule algorithms in one owned
worker and solver. The source default uses a separate preamble verifier and a
worker pool; native parallel scheduling remains pending. Repeated public session
runs recreate the owned context and replay source preambles, rather than retain
a process across resets. Unsupported semantics and requested runtime policies
return explicit errors. Native CLI exit codes distinguish success (0), failed
proof obligations (1), and input/configuration/execution errors (2).

Ferrum's `--parseOnly` actually loads and parses the source and its imports,
matching the option's documented purpose. The pinned Silver runner instead exits
in `prepare` because `SilFrontendConfig.exit` includes `parseOnly`; Ferrum does
not reproduce that early-return bug. Native help covers common options; exact
Scallop help, abbreviation and diagnostic compatibility remains pending.

The native CLI reports source dependency metadata and elapsed time, honoring
`--dependencies` and `--no-timing`. Elapsed time uses a monotonic Rust clock
instead of wall-clock subtraction; common result wording retains Ferrum naming.
