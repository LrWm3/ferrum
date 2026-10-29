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
Domain-instance type substitution currently forces reconstruction, so unchanged
node identities can differ from Scala while reconstructed metadata and return
types are retained. Exact reuse during that substitution remains a porting gap.

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

The optional `native-z3` feature implements the Z3 C API contracts directly with
thread-bound, context-owned handles and kind/context checks before FFI calls.
The API CLI requires the pinned 4.16.0.0 library instead of attempting execution
with a mismatched library. Assertion handling proves a goal only on UNSAT and
attempts scope restoration on error. Structured failure models retain their Z3
context. Non-reference-counted contexts keep AST allocations until their last
handle is dropped, a memory-lifetime difference from the Java binding.
Unknown solver parameters warn and are skipped, matching the source; invalid
typed values remain errors. Context arguments are restricted to documented Z3
context keys because the C configuration API cannot report unknown keys reliably.
Random seed values use the source range with a native sequence. These choices
and focused solver checks do not establish complete native API parity.

Debug tokens retain the source ASCII grammar. `debug@` is lexically accepted
upstream but its split-index construction fails; native construction reports a
specific error. Debugger input/worker/solver services propagate typed failures;
the interactive loop, complete printing and debug failure-context assembly are pending.
The dormant flyweight annotation has an explicit native pool rather than a new
procedural macro. Concurrent creation returns the canonical stored handle.

## SIF extension type inference

The source `lowEvent` parser extension exposes an empty substitution list, which
causes Scala to skip enclosing operator unification. Ferrum retains that extension
state and supplies a concrete Boolean identity candidate at the operator boundary.
This permits Boolean combinations such as `lowEvent && low(x)` while rejecting
arithmetic uses such as `lowEvent + 1` during native type checking.


## Native execution assembly

The first concrete runtime composes the translated rule algorithms in one owned
worker and solver by default. Explicit `--numberOfParallelVerifiers N` with
`N > 1` uses a separate main prover and a native worker pool; the source default
selects a pool based on available processors. Worker solvers are constructed and
destroyed on their owner threads. Repeated public session runs recreate the
main context and pool and replay source preambles, rather than retain processes
across resets. Submitted tasks are drained on an execution error so warning and
scope delivery finishes before returning; dropping a pool cancels queued tasks
and waits for active calls. Active solver interruption is not connected yet. Unsupported semantics and requested runtime policies
return explicit errors. Native CLI exit codes distinguish success (0), failed
proof obligations (1), and input/configuration/execution errors (2).

Ferrum's `--parseOnly` actually loads and parses the source and its imports,
matching the option's documented purpose. The pinned Silver runner instead exits
in `prepare` because `SilFrontendConfig.exit` includes `parseOnly`; Ferrum does
not reproduce that early-return bug. Native help covers common options; exact
Scallop help, abbreviation and diagnostic compatibility remains pending.

Method filters preserve whole-name inclusion followed by exclusion. Native
matching accepts ASCII letters, digits, underscore, dot, star, question mark,
alternation, and escaped literal dot/dollar after source wildcard conversion.
Other Java regular-expression constructs return an explicit unsupported error;
they are not silently interpreted with different Rust regex semantics.

Generated native worker identifiers use underscores so SMT symbol sanitization
leaves them unchanged. This preserves source counterexample lookup by raw term
identifier. The CLI retains diagnostic IDs while using source readable messages
to include failure contexts. Alternative function ordering follows the source
call graph; incomparable SCCs may receive different numeric heights because Rust
and JGraphT iteration order differ.

The native CLI reports source dependency metadata and elapsed time, honoring
`--dependencies` and `--no-timing`. Elapsed time uses a monotonic Rust clock
instead of wall-clock subtraction; common result wording retains Ferrum naming.


## Native verification stack

Pinned Silicon `build.sbt` configures both run and test JVMs with `-Xss128m`.
Ferrum's file runner constructs plugins and solver contexts inside a native thread
with the same 128 MiB stack setting. Direct AST sessions retain caller-thread
ownership; embedders choose the stack when creating that thread. No native Z3
context is transferred between threads. The evaluator's large dispatch body is
split into non-inlined expression families without changing continuation order.
Both runtimes still have finite stacks; recursive inputs can exceed that bound.

## No-trigger snapshot-map templates

The pinned `field_value_functions_axioms_no_triggers.smt2` refers to the value
type in `$FVF<$T$>`, while its contributor declares `$FVF<$FLD$>`. The predicate
counterpart similarly uses `$PSF<$S$>` instead of `$PSF<$PRD$>` and contains an
unsubstituted `$FRD$` domain placeholder. These produce undeclared SMT sorts or
symbols when `disableISCTriggers` is enabled. Ferrum corrects those three
references during template instantiation, for fields, predicates and wands.
Bundled upstream resource bytes and the triggered path remain unchanged.

## Native report output

Reporter writes and flushes propagate native I/O errors, extending the explicit
writer behavior above to StdIO reporters; Java PrintStream suppresses these errors.
Exception messages carry the display text, stack and optional cause captured at
the origin. Rust cannot recreate a JVM stack or erased collection implementation
from an error or Vec: missing source-rendering provenance remains unsupported.
Time formatting retains the source f32 division and Java half-away-from-zero
rounding, but uses a stable decimal dot rather than the JVM default locale.

## Linked mask-heap solver transport

The pinned Silicon `TermToZ3APIConverter.scala` does not handle mask heap sorts
or terms: even a field example with `--prover Z3-API --maskHeapMode` throws
`scala.MatchError: Hp[Int]` during sort declaration. Ferrum's linked mask bindings
are an explicit transport extension using the pinned `TermToSMTLib2Converter.scala`
and mask preamble names and signatures. Mask semantic comparisons therefore use
the pinned Scala stdio route. Linked Z3 4.16 checks compare against those stdio
results, not against successful Scala API execution. This extension does not
change the source mask verification rules or establish general encoding soundness.

## Mask function integration boundaries

Reentry into a function's current phase reads an immutable view sharing its source
identity. Computed frame data is cached under that identity; a genuinely recursive
frame-construction cycle returns an explicit unsupported error. This boundary has
not been shown equivalent to upstream's recursive construction. Ordinary recursive
trigger reentry and quantified-frame fixtures have positive/negative source checks.

Mask mode combined with ordinary function calls in domain axioms is rejected before
solver emission. Pinned Silicon's domain translator supplies a Unit snapshot even
when mask function symbols have a different state-argument signature, causing an
unknown-precondition-function solver error on the same inputs. Ferrum preserves
the unsupported combination with an earlier diagnostic.

## CFG output filenames and failures

Standalone graph dumps use `CFG<n>.dot` with a process-local numeric identity
shared by clones of a SilverCfg. This replaces the JVM's System.identityHashCode;
filenames are not persistent graph identifiers. Method dumps retain `<name>.dot`.
The source DOT structure, block IDs, iteration order and escaping remain intact.
Native rendering and file-write errors propagate instead of being suppressed by
Java PrintWriter, consistent with the native I/O difference above.

## Native plugin exception stacks

Silver SilFrontend.execute reports PluginException with the JVM stack captured
by the thrown exception. Ferrum captures a Rust backtrace when its missing-plugin
error is constructed, together with the actual error display. The payload is
explicitly labeled Native Rust; frames and symbol availability depend on the
native build. An opaque resolver error can only be captured at the external
resolver boundary and is labeled accordingly. Direct reset retains its original
typed error, while concrete execute reports the captured exception and preserves
the plugin error if reporting also fails. Focused provider checks exercise the
actual StdIo path and plugin/reporting failure combination.

## Execution trace lifetime across runs

Pinned Silicon FunctionVerificationUnit.reset retains postConditionAxioms when
DefaultMainVerifier resets its existing function supporter. Ferrum currently
constructs a fresh context, factory and function unit for each native session
run, so its internal trace contains current-run function postconditions only.
The trace uses the actual ordered domain contributor axioms, excluding
uniqueness and collection preamble blocks, and the main function unit records.
Cross-run trace compatibility remains incomplete; prior terms are not copied
across unrelated factories. Public advanced reporting stays gated.

Parallel trace callers must install the shared run logger and a local record
factory in every worker. Ferrum checks their identity before traced method/CFG
execution and rejects missing setup. This is an explicit assembly requirement
when a logger owner is explicitly installed. The native factory now propagates
that owner to main and workers; source-compatible decider formatting and public
logging configuration remain incomplete.

Run logger shutdown waits for native worker threads before closing the shared
root. An extra internal pool `Rc` makes explicit stop retain the context and
logger for a later retry. Production clones are confined to the main prover and
lexical verification call, which end before backend destruction. A future private
caller that retains a pool clone beyond backend destruction would violate this
invariant: eventual root closure is not guaranteed in that case. Worker attachments
do not own shutdown authority.

Timeout reporting follows Silicon.scala's explicit empty domain/postcondition
axiom lists and retained member logs. Native cleanup waits for worker quiescence
before root close/reporting. The same root survives timeout and subsequent reset.
As in StateReporting.scala, closing a scheduled state reporter is permanent:
reused roots can record members, but do not restart scheduled callbacks.

## Diagnostic collection notation

Native trace and state reporting uses `Seq(...)` for erased Scala sequence
implementations in predicate lookups/permissions/triggers and macro hints, and
`Set(...)` in native iteration order for distinct-symbol sets. Term/product names
and operands are retained, but JVM List/Vector spelling and hash-set iteration
order are not reproduced. Custom value-based log filters compare these displayed
native strings and must use this notation for the affected values.

The adaptation is restricted to diagnostic rendering. Counterexample model lookup,
strict chunk rendering used to compare debug heaps, term identity and SMT emission
keep their existing paths. This avoids changing verification or model lookup to
recover incidental collection display provenance.

## Native statistics numbers

The native statistics formatter uses Rust's finite floating-point debug notation,
which round-trips to the same binary value, including negative zero. NaN and
infinities use Java-compatible spellings. Java 17 FloatingDecimal may choose
different digits or exponent notation (for example, `1e23` and the minimum
subnormal), so this is a declared diagnostic adaptation rather than byte-for-byte
JVM formatting. Callers can still supply an exact formatter. Integer deltas retain
the source path; Java hexadecimal floating-point input remains unsupported.

## Missing standard imports

Silver loads standard imports from JVM classpath resources and includes the Java
exception in a missing-resource diagnostic. Ferrum uses bundled native resources
and identifies the same `import/` resource path as missing from those bundles.
The parse error category and import statement position are preserved.

## Invalid macro expansions in resource operands

When a macro expands to a non-resource expression inside a resource operand,
Silver reports a parse-tree duplication exception containing a Scala AST dump.
Ferrum reports a parse error at the same enclosing expression and describes the
required resource operand without reproducing runtime-specific AST internals.


## Source exception reporting and native error preservation

The native frontend now connects Silicon's `disableCatchingExceptions` setting
and exception reporter events. Explicit source prover-protocol and external-tool
failures retain their source classes and messages. Verification catches convert
those failures through the ported `exceptionToViperError` mapping; startup reports
use the frontend logger and preserve startup failure. Disabling catches propagates
the typed failure. Warning delivery, reporter rejection and cleanup failures stay
visible together with the original failure instead of being discarded during
conversion.

Malformed quantifier counts and repeated linked-Z3 assumption errors carry actual
native error messages and captured Rust backtraces. Ferrum does not fabricate JVM
stack frames or classify arbitrary Rust panics and unsupported port paths as source
exceptions. Rust writer errors remain explicit as described above. Nine integrated
exception/protocol tests pass with real stdio and linked Z3, including malformed
responses, EOF, invalid startup/version, assertion and assumption retry failures,
reporter rejection, and cleanup; the workspace all-target check also passes with
`native-z3`. These are focused exception checks, not complete compatibility claims.
