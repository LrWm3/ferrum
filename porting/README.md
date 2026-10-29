# Port status and checks

The description pass covered all 336 mapped Silver/Silicon source and test files.
The Cargo workspace now has 409 mapped and assembly modules. `described` files
remain comment-only; `skeleton` files contain partial implementations with explicit
gaps; `ported` means translated bodies compile, not that compatibility has been
proved. Reviewed progress and remaining work are recorded per file.

The CLI connects configuration, parsing, default plugins, consistency checks and
source-shaped Silicon rules to the native Z3 stdio transport. End-to-end smoke
checks cover valid and invalid ordinary methods, contracts, branches, allocation,
field permissions and method calls. Unsupported features return execution errors.
The default runtime currently uses one worker. Loops, fold/unfold, scoped
unfolding, heap-independent quantifiers, generic domain axioms and nested
Seq/Set/Multiset/Map instances now reach Z3. The source thresholded type closure
connects recursive domain dependencies and ADTs inside collections.
Impure branch joins preserve conditional ownership and consumed snapshots in
focused positive and negative checks. Pure and heap-dependent functions now run
the source contract/body phases and use recorded snapshots for their axioms.
Interpreted backend types, including bitvectors and floating-point values, now
reach their source SMT operations and snapshot wrappers. Field and predicate
quantified permissions, ForPerm, heap-dependent triggers and recursive-function
predicate triggers now reach the native solver. Independent checks cover 27
quantified-resource cases, including fractional ownership, consumed permissions,
disjoint snapshots and failing assertions; 21 function cases and four existing
native runner regressions also pass. Remaining trigger forms and advanced reporting
still need broader compatibility checks. No comparative speed improvement
has been established.
Single-resource and quantified heap havoc now replace selected snapshots while
preserving permissions and unrelated chunks. Independent CLI checks cover aliases,
guards, noninjective receivers, fractional permissions and old call snapshots;
the permanent havoc regression passes through both solver transports.
Magic-wand packaging, application and applying expressions now run through both
transports. Independent checks cover 29 positive and negative cases, including
transferred footprints, consumed wands, nested packaging, conditional resources,
quantified wands and `old[lhs]` snapshots. The permanent regression checks that
packaging removes transferred permissions and that application consumes the wand.
Quantified field and predicate transfers inside packages now preserve source
reserve-heap consumption, inverse axioms and snapshot summaries. A frozen 57-case
matrix across all three quantified exhale modes passes through both transports,
including split permissions, disjoint values and missing footprints. A permanent
regression checks transferred ownership and preserved values. This focused
coverage does not establish full source compatibility.
Wand proof scripts now check the source empty-reserve invariant before assertions,
then preserve asserted permissions for the remaining proof. Seven valid/invalid
value, footprint, quantified-resource and conditional cases pass on both
transports; the permanent wand regression exercises repeated proof assertions.
More-complete and on-demand exhale (`--exhaleMode 1` or `2`) and CFG joins
(`--moreJoins 2`) now connect the source summaries, permission consumption and
branch merging. A frozen suite of 115 cases passed through both solver transports,
covering aliases, missing/zero/fractional ownership, functions, predicates with
collection arguments, conditional heaps, loops and wand combinations. Nine
permanent native CLI regressions also pass. An explicit `--numberOfParallelVerifiers N` now selects a pool for `N > 1`;
the native default remains one worker. Functions and predicates are verified once,
then source-ordered preambles and retained axioms reach thread-owned solvers.
Methods and supported standalone CFGs are dispatched to workers and results are
collected in source order. Warnings are drained before returning, including when
a worker fails; each repeated Session run recreates its main solver and pool.
Two-worker checks cover 68 function/domain/quantified-resource cases, real failing
methods, warning delivery and repeated-run axiom isolation. Nested branch
parallelism and advanced profiles remain incomplete;
standalone CFG-only contributor analysis has upstream TODOs. No parallel speedup
has been measured against upstream.
Global `--timeout` now covers backend verification and result assembly, after
frontend processing and solver startup. Expiry cancels pending tasks, repeatedly
interrupts active solver calls and waits for owner-thread cleanup before returning
`timeout.error`. Cleanup and interrupt errors remain visible as warnings. Native
Rust operations observe cooperative checkpoints, so this is not a hard wall-clock
bound for every preprocessing or cleanup operation. Timeout followed by reuse of
the same Session passes with one/two workers on both transports. Pool cancellation
checks cover blocked stdio reads, active linked queries and cleanup failures.

Source consolidation modes, quantified chunk ordering and the distinct
`disableCaches` / `disableValueMapCaching` policies now reach the native context.
Method inclusion/exclusion uses whole-name matching in both sequential and pooled
execution; functions and predicates still run independently of method selection.
A 126-case matrix passes through both transports. The source minimal consolidation
mode remains incomplete for some aliased fractional permissions. Native method
filters currently accept a shared subset of Java/Rust regular expressions and
reject unsupported syntax explicitly.
`enableSimplifiedUnfolds` now replays the source predicate-content trees:
substituted assumptions, scaled permissions, quantified singleton snapshots and
branch joins. Predicate data is shared with method workers; expression unfolding
uses the source join distinction. Independent checks cover ordinary/nested and
fractional predicates, expression unfolding and quantified field/predicate bodies
across all three join modes on both transports. Selected outcomes also match the
pinned Scala reference. Wands inside predicate bodies remain rejected by Silver
consistency; debugger-specific replay remains unsupported.
`disableISCTriggers` now connects the source no-trigger rules and preambles.
Ten positive/negative field, predicate and wand cases pass through both transports.
Three pinned template-name defects are corrected during instantiation, as recorded
in [differences.md](differences.md).
Custom Seq/Set/Multiset/Map axiomatization files now replace their bundled sources
only when the corresponding collection is used. Relative and standard imports,
source analysis and successful-program caching are connected. The cache follows
the pinned source's root-path/modification-time policy: changing only an imported
file does not invalidate its root entry. Used malformed sources fail explicitly;
unused ones are not loaded. Full/stripped axioms, generic domains and quantified
resource dependencies are checked on both transports; selected full/stripped
outcomes also match the pinned Scala reference.
Quantifier preprocessing now runs bottom-up on pure `forall` and all `exists`
expressions, with standard trigger selection and the source arithmetic-rewrite
fallback. Typed warnings and trigger choices reach configured reporters immediately;
reporter failure stops traversal. Conditional-permission rewriting then runs before
contributor analysis; `printTranslatedProgram` prints that rewritten program.
Ninety-four cases per transport cover function/domain/quantified-resource regressions,
conditional resources, existentials and warnings. Printed standard/arithmetic
trigger programs match the pinned Scala output, and a direct context probe checks
positioned warning/trigger ordering and reporter failure propagation. Standalone
CFG trigger preprocessing retains the upstream TODO.

Native failures now capture available solver models in all five source views,
restore caller stores on method/function precondition failures and render failure
contexts in the CLI. Branch-condition reporting and the alternative function
verification order are connected. Twenty direct Session model cases and seventy
CLI cases pass per transport, including one/two-worker value checks; all fifteen
permanent native CLI regressions pass on both transports. A reproduced linked-Z3
fractional-function model crash is fixed by retaining interpretation/entry handles.
Counterexamples still have explicit unsupported model/heap forms; debugger profiles
require further integration. `reportReasonUnknown` now preserves the source
distinction between an absent reason and a recorded solver reason, including
literal `null` after soft assertions. `proverRandomizeSeeds` emits one shared seed
vector per stdio run; the API route keeps the source per-context randomization.
Thirty-six one/two-worker CLI checks cover assertion modes, counterexamples, seeds
and API log options; the reason text also matches the pinned Scala reference.
Low-level owners reusing NativeOptions must call `reset_seed_epoch` once after
all old workers stop and before starting the next shared run. Session does this
by constructing fresh options.

The opt-in SIF plugin now connects paired domain/permission values, relational
predicate helpers, optimized loops and AST return/termination control. Source
`old` assertions and inactive `inhale false` guards retain their transformed
obligations. A frozen 66-case CLI suite and ten constructed-program cases passed
through both solver transports, along with positive/negative ForPerm probes.
AST break/continue, exception, try/catch/else/finally and inlined-call control
now connect the source activation flags and restoration order. A further 35-case
constructed-program matrix passes on both transports, including failing assertions
after control transfers. Broader relational compatibility remains unproved.
Programmatic dynamic checks and `Low` comparator functions now follow source
lookup, type substitution and traversal order. A 66-case constructed-program
suite passes through both transports, including controls, dynamic assertions,
relational predicates and direct/nested comparators. Nested `Low` within `Low`
and alternate SIF configurations retain explicit unsupported boundaries.
Relational unfolding, impure quantified predicates, direct programmatic Assume
and direct all-low helper calls now follow source activation guards and priming.
Sixteen focused CLI/AST cases pass per transport, including inactive branches,
permission consumption and failing assertions; 25 SIF unit tests and existing
loop/inactive-inhale regressions pass. The programmatic Assume probe lowers
assumptions after product construction; the normal textual frontend lowers them
earlier. All-low function generation remains gated.

Frontend parsing now retains sibling import failures, macro name/proof-script
reports and warnings in source order, and uses source-aware node rendering for
consistency diagnostics. Macro copying also handles versioned identifiers and
already-expanded sequence products. Imported macro failures are caught per program
so sibling reports survive; definition/call spans and argument/body-kind messages
match the checked Scala fixtures. `elseif` chains now translate to nested conditionals.
All 283 Silver unit tests and ten independent CLI cases pass. Full diagnostic
compatibility remains incomplete; failed macro expansion can leave transient parse
nodes partially rewritten, but those programs are rejected before analysis.
ARP now traverses typed statement extensions, including TryBlock children.
Focused checks preserve permission reads, TryBlock fallback and later failures.
ARP-generated method-call locals inside TryBlock still expose the pinned source's
CFG/executor scope gap: these programs fail with a missing store value rather than
verify. The port retains that limitation and records the source locations.
Domain-axiom typechecking now allows ordinary function calls only when they have
no actual `requires` clause, matching the pinned resolver. The native contributor translates calls with the source Unit snapshot and
conjoined precondition symbols, declaring all contributor symbols before axioms.
Positive and negative source fixtures now reach the intended result on both Z3
transports, while preconditioned calls remain rejected. Combining ordinary-function
domain axioms with mask heaps retains the pinned source solver-signature failure;
mask function symbols use a different state-argument signature. Ferrum reports
that combination as unsupported before sending malformed terms to the solver.

- [sources.toml](sources.toml) pins the two semantic baselines.
- [modules.toml](modules.toml) maps every source file to its Rust destination and
  records reviewed progress. Symbol outlines live in the destination comments.
- [resources.toml](resources.toml) records unchanged embedded upstream resources
  and their checksums.
- [non_rust_files.tsv](non_rust_files.tsv) accounts for the other 1,993 tracked
  upstream paths, including fixtures, resources, documentation, tooling and the
  duplicate Silver submodule. Dispositions are provisional plans, not completed
  asset imports or exhaustive content reviews.
- [conventions.md](conventions.md) separates shared requirements from open Rust
  representation choices. [differences.md](differences.md) records adopted
  behavioral departures.

Three `gpt-6.1-terra` agents read source files and their relevant collaborators,
wrote separate batches, and performed targeted peer reviews. Coordinator review
included representative source/brief comparisons, mapping and stage checks, and
reconciliation of peer corrections. Higher-risk peer checks covered parser and
plugin transformations, state merging, heap encodings, retries, continuations,
quantified permissions, snapshot caches and function-axiom phases. This does not
prove code correct or replace the broader testing pass in [PLAN.md](../PLAN.md).

Every one of the 269 mapped production source files now has a first Rust
implementation, with remaining work recorded explicitly. The workspace has
activated every module and embedded the pinned resources. It includes typed
ASTs, checked parser/frontend subsets, CFG lowering,
plugin transformations, terms and heap representations, solver process transport,
and translated symbolic execution, permission, predicate and function algorithms.
Several algorithms depend on explicit service traits that still need concrete
implementations. Unsupported paths return errors; they must not imply successful
verification.

Focused checks cover specific identity, translation, traversal and solver-protocol
questions. Review has already caught differences in rewrite recursion and AST
location traversal; corresponding regressions accompany the fixes. These checks
are not a substitute for the compatibility campaign in the plan.

Of 67 source-mapped files under `tests/upstream/`, 66 intentionally remain briefs
for the later broad testing pass in PLAN.md. `TestInput` already has grouping/tag
helpers; it is not a completed suite. Production `testing/` helpers are part of
the implementation pass. A source module having a Rust body marks first-pass
coverage only; it does not close the gaps listed in its header
and inventory entry.

The final first-pass workspace checks, build and test-target compilation passed
with the lockfile and offline dependencies. Clippy completed with warnings about
source-shaped type/API complexity, nested conditionals, mutable key types and
other cleanup items; these remain review work. Subsequent native integration
checks distinguish successful verification (exit 0), proof failure (exit 1), and
syntax/unsupported execution errors (exit 2). The source frontend and diagnostic
regressions pass; the broad upstream compatibility suite has not been run.

Run the inventory and implementation checks from the repository root:

```sh
python3 tools/check_porting.py --complete --upstream
cargo fmt --all --check
cargo check --workspace --all-targets --locked
git diff --check
```

The optional `native-z3` feature links a native Z3 library without Java or JNI.
The CLI's `--prover Z3-API` path requires version 4.16.0.0, matching the pinned
Silicon API backend. Builds without the feature keep using solver subprocesses
and do not link `libz3`. Supply a matching library at build and run time, for
example on Linux:

```sh
Z3_LIB_DIR=/path/to/directory-containing-libz3
RUSTFLAGS="-L native=$Z3_LIB_DIR" cargo build --features native-z3 --locked
LD_LIBRARY_PATH="$Z3_LIB_DIR" target/debug/ferrum --prover Z3-API input.vpr
```

The reviewed Linux library came from the official
[Z3 4.16.0 release](https://github.com/Z3Prover/z3/releases/tag/z3-4.16.0),
`z3-4.16.0-x64-glibc-2.39.zip`, with SHA-256
`7288c49a5bd6dbafd7b0b0d1f65956b91672da24b08f09242919af159be3418e`.
This archive is platform specific; Ferrum does not download or install it.
Both assertion modes, typed startup solver parameters and invalid-trigger retry are
connected. Documented Z3 context keys can be supplied with `--proverArgs key=value`;
unsupported context keys return errors. Source solver warnings reach the CLI.
The API route ignores stdio transcript-log options, matching pinned Z3ProverAPI;
remaining runtime reporting is incomplete. Dynamic options remain
unsupported, as in the source API backend. A non-reference-counted Z3
context retains AST allocations until the context and its last handle are dropped;
long-lived API contexts can therefore retain more memory than the Java binding.

The file runner uses a dedicated thread with a 128 MiB stack, matching the pinned
Silicon launcher's `-Xss128m`. Plugins and native solver handles stay on that
thread. Direct AST `Session` users control their own thread and should create the
session inside a thread with `VERIFICATION_STACK_SIZE` for recursive inputs.
The evaluator dispatches to separate expression families to reduce large Rust
frames. A 32-level predicate fold/unfold regression checks both a preserved value
and a failing assertion through both transports. This remains a finite stack
limit; it is not a guarantee for arbitrary verification depth or a speedup claim.

Run the native runner regressions with `FERRUM_TEST_Z3=/path/to/z3` for stdio, or
`FERRUM_TEST_PROVER=Z3-API` with the feature and matching library environment:

```sh
FERRUM_TEST_Z3=/path/to/z3 cargo test --test native_cli -- --ignored
FERRUM_TEST_PROVER=Z3-API RUSTFLAGS="-L native=$Z3_LIB_DIR" \
  LD_LIBRARY_PATH="$Z3_LIB_DIR" \
  cargo test --features native-z3 --test native_cli -- --ignored
```

`--upstream` requires the pinned Git objects in the sibling checkouts named in
`sources.toml`; omit it for local document checks without those checkouts. To
check selected descriptions while editing, pass their repository-relative paths.
The checker validates inventory coverage, unique destinations, source links,
stage-specific documentation requirements, comment-only contents for files still
marked `described`, attribution for translated code and copied resource bytes.
`--complete` means all source descriptions exist or have progressed; it does not
mean all implementations are complete. Source-specific prose and implementation
semantics still need review; these checks do not establish behavioral compatibility.

When implementing a file, retain its pinned source reference, update the brief
and inventory, and replace the description-stage checks with the implementation
checks in the plan. Resolve cross-file representation choices before treating
proposed signatures or ownership as settled.

Reporter adapters now render source entity/branch results, chosen triggers, verifier
states, statistics, outlines, definitions and CSV traces. Exception rendering accepts
origin-captured details and rejects absent provenance. Runtime Scala collection and
parse-program fallback strings and advanced runtime delivery remain incomplete.
Eight focused reporter checks and workspace all-target checks pass; an independent
80,000-value JVM comparison covers the source f32 time conversion and rounding.

Mask-heap lower layers now implement source single/quantified production and
consumption, transfer steps, snapshot adaptation, havoc, function frame construction
and identity-preserving phase snapshots. The native runtime now connects these adapters through `--maskHeapMode`
and optional `--simplifyOnConsume`. The linked converter
includes the corresponding SMT-LIB bindings and a regression for recursive alias
expansion; pinned Scala API mask support differs as documented below.

Expression utilities now traverse reconstructible plugin expressions when projecting
Boolean proof-obligation guards. The source name-based variable renaming API also
renames bound declarations, preserving first-match behavior and declaration
position/info; capture-avoiding instantiation remains a distinct operation.
Extensions without reconstruction hooks still fail explicitly.

Mask runtime integration covers empty heaps, field reads/writes, predicate
fold/unfold and unfolding expressions, single/quantified consumption, wand
transfers, ForPerm, havoc and source function frames. Function phase emission
retains source declaration/assumption order; readable phase snapshots avoid holding
a mutable function-data lock across recursive trigger translation. The permanent
regression exercises predicate reads, disjoint quantified wand transfers and
recursive trigger reentry with one/two workers and simplification off/on.
The assembled snapshot matched all 248 expected outcomes per transport in a
124-input matrix covering both simplification modes, and all 19 permanent CLI
regressions passed on both transports. Mask timeout/session reuse also passed
on both transports and worker counts.
These checks are bounded; full source compatibility and performance remain open.

Permission-expression scaling now traverses typed plugin children while retaining
nested wand/type errors. Quantified-permission desugaring preserves an unhandled
extension RHS as the original quantifier, matching the source fallback; later
consistency and execution checks still reject unsupported expressions.

Parallel-branch prerequisites now capture and replay path conditions, fresh
functions/macros, solver options and error counts on another verifier, and restore
the caller after a cooperative join. A two-solver check covers replay and returned
declarations. This does not enable `--parallelizeBranches`: owned continuations,
cooperative scheduling, branch-report ordering and cancellation integration remain.

`--printMethodCFGs` now writes source DOT graphs for selected methods and standalone
CFGs under `--tempDirectory`, at the source verification hooks. Rendering retains
block identities and insertion order; unsupported AST printing and native I/O
failures return errors. Cloned CFG handles share their output filename identity.
A selected conditional-method dump matched the pinned JVM output byte for byte.
Focused checks cover method filtering, output errors and standalone CFG dumps
with one/two workers.

The parse reformatter now handles ordinary members, statements, types, expressions,
specifications, triggers and comments, plus opted-in refute, smoke, ARP, predicate
instance, SIF, termination and TryBlock products. Twenty-two bounded formatting
comparisons match the pinned JVM (18 ordinary cases and four plugin groups).
Unknown extension formatting remains incomplete. Source quirks are retained: SIF low/lowEvent/rel parse products
lose their keyword/punctuation in the source formatter and can produce malformed
text; this change does not silently repair that source behavior.

ADT parsing now retains source bracket/brace, separator, derives and without
wrappers, sharing semantic node handles with name analysis and translation. ADT
products consequently use the same source formatter, including its `}derives`
spacing quirk. Seventeen focused ADT parser/type/encoding checks and three JVM
formatter comparisons cover generic parameters, constructors, derivations, comments,
empty lists and annotations; broader compatibility remains open.

Native reporting now renders source let/application-hint terms, mask predicates
and dummy heaps, resource maps, heap/snapshot wrappers and basic mask chunks.
Retained Silver field/predicate nodes use their source pretty printer; wand IDs
and insertion order remain intact. JVM oracle examples and focused formatter
checks cover these products. Renderers still reject cases requiring erased Scala
collection provenance or unsupported AST products.

Worker pools now support cooperative waiting on owned nested tasks, retaining
owner-thread solver access and cancellation/panic bookkeeping. Evaluation joins
use owned expression/value/short-circuit actions and per-branch entry buffers;
concrete worker jobs transfer path conditions, options, fresh declarations and
assumptions and return join entries/declarations. Branch errors retain their
warnings instead of leaking them to later jobs. Shared dispatch still handles
ordinary method/CFG tasks through their existing lifecycle and reporting paths.

This is infrastructure, not an admitted parallel branch mode. Runtime queue
injection, result/report ordering, error-warning delivery and active cancellation
coverage remain. A path-stack identity token changes on start/reset/replacement
and remains stable across scope operations, matching the source reference check;
future code must use the replacement API rather than assign the public field.

The AST and reformatter providers now create their source no-op construction
verifier, apply supported shared configuration and rebuild configured plugins on
reset. The reformatter keeps macros unexpanded; ordinary parsing still expands
them. Parse-only construction completion emits the source success/failure messages
and never starts a solver. Plugin disabling, duplicate warnings and configuration
errors retain source ordering. Provider checks cover reset, macro retention,
parse errors and construction reporting. Reporter manager rebinding/configuration,
custom plugin resolution and full command-line orchestration remain incomplete.

State-report records now have a native adapter for ordinary expressions,
statements, members, terms and chunks. It retains source positions and concrete
node downcasts for reporter consumers; unsupported node printers still return
errors. This completes the ordinary rendering boundary, while timed polling and
member execution hooks remain to be connected.

The PAST provider now constructs its no-solver verifier, applies supported
configuration and plugins, and runs parsing plus semantic analysis without
translation or verification. Its inherited finish path transforms diagnostics,
runs plugin finish hooks, keeps the first duplicate readable error, stores the
result and emits the source overall message. Shared reporter reset hooks and
complete command-line orchestration remain open.

The recording log root now owns ordered member logs and their shared ID counter,
constructs method/function/predicate records, closes retained logs and renders
their trees. Configuration files preserve the source line-joining behavior and
warn before falling back to defaults on read/JSON/product errors. Files use UTF-8
and native error details. The pinned source's close behavior is retained: it
closes existing member logs without permanently closing the root. Timed-state
composition and verifier event producers remain separate integration work.

Internal parse function types now use the source implied delimiters in the
reformatter, including its trailing comma for nonempty arguments. The two focused
empty/nonempty cases match the pinned JVM; this adds no parsed-language syntax.

Custom expression plugins can opt into ordinary name traversal, type inference,
substitution and translation using child callbacks. A bounded keyword plus one
parenthesized-expression parser hook connects registered plugins to those phases.
Hygienic macro copying can reuse the grouped-expression copier and retain delimiter
positions; missing hooks return unsupported errors. Focused positive/negative
checks cover parsing through checked translation and macro argument substitution.
This does not provide a general parser-combinator or custom binding-scope API;
the pinned source's PScope trait is sealed.

State reporting now has an owned fixed-delay polling worker with lazy startup,
restart after the last member unregisters, and permanent shutdown. Recording and
discard-only member logs forward source data/scope/branch events, including
records excluded by log filters. Configuration selects disabled, state-only,
advanced recording or combined modes, reading the log config only for advanced
recording. Per-member reporting failures do not stop other member reports.
Shutdown joins outside logger locks; a blocked callback can delay it. Callback
self-close signals shutdown without joining its own thread, whose dependencies
remain owned until it exits. Verifier event/lifecycle wiring and advanced trace
emission are still incomplete; public reporting profiles remain gated.

Joined CFG branches now carry owned edge/join/path actions, and predicate-content
branches carry owned subtree/replacement actions. Their post-join continuations
remain local, and execution remains synchronous. Alternate CFG path IDs are still
allocated lazily. These are source-eligible boundaries for future scheduling;
expression joins explicitly disable parallelism in the pinned source. The public
parallel-branch flag stays gated. A rejected evaluation-scheduling experiment is
not part of the admitted port.

Provider-owned phases now emit source parsing and typechecking warning events in
order, including an empty parsing-warning event on success and no such event on
parse failure. Reporter errors propagate before committing the phase state. The
standalone facade keeps its existing warning collection path. Focused checks cover
warning delivery on successful/failed analysis and reporter failure during either
phase. Shared reporter configuration/plugin rebinding remains separate.

The injected-AST frontend now accepts a backend factory that configures the
verifier once and returns its effective shared configuration, including backend
options. It builds configured standard/custom plugins and preserves the pinned
source's starting state (and consequently skipped consistency phase) and retained
errors across repeated calls. Native invalid/exit configuration rejection remains
an explicit deviation from the source initializer. Focused tests use a stub
backend; a concrete Silicon verifier adapter is still required.

Native evaluation, production and retry-local consumption now preserve symbolic
scope IDs through successful continuations, leaving failed paths open as in the
source. An owner-local factory retains complete persistent states and snapshots of
path assumptions without requiring every generic context to be thread-safe. Active
logging without a factory returns an error; disabled logging preserves existing
behavior. Local hook checks inspect record types, retained state and disabled/error
paths. Run/member installation, worker migration and remaining progress events
are still incomplete, so public reporting profiles remain gated.

The public `NativeFrontendApi` now connects injected Silver programs and source
plugin processing to an owner-thread native Session. Backend-aware configuration
is parsed once, Silicon's mandatory backend consistency check is retained, and
explicit stop errors propagate through a new fallible verifier lifecycle hook.
A caller-owned warning sink captures initialization, verification and cleanup
warnings; plugin-initialization failure drops and stops the new session. Real
Z3 checks cover positive/negative programs, repeated calls, consistency rejection,
shutdown, initialization warnings and process cleanup, including linked Z3.
The caller supplies a thread with sufficient verification stack space. Dependency
metadata, exact reporter events and plugin-aware reporter rebinding remain open.

Optional run-owned logging now opens/closes method, predicate and function member
scopes at source lifecycle points. Fatal proof results close a completed function
scope; service or option-cleanup errors leave it open. Active roots require a
full-state factory before registration. Focused lifecycle checks pass; the root
is still not installed by ordinary verification sessions. Additional progress
events and top-level shutdown attachment remain before reporting profiles can be
enabled. Source configuration forbids combining ordinary parallel branches with
advanced logging or stalled-state reporting.

Joined CFG branches now have an internal owner-thread queue scheduler, cooperative
waiting, source-ordered join entries, declaration transfer and branch-failure
reporting. Worker solvers reserve their preamble scope lazily after broadcast;
independent queued members and foreign branches restore the suspended worker's
path conditions, options and error count. Deterministic negative controls exposed
false proofs without the reserved scope or foreign-state restoration; corrected
real-Z3 cases cover queued methods/CFGs, reset, nested branch ordering and active
cancellation. Both stdio and linked Z3 cover one/two-worker joined CFG execution.
The public parallel-branch option remains gated: nonjoined continuations and
other eligible branch families are incomplete, and logger migration is not wired.
Expression joins remain synchronous as required by the source. Standalone CFGs
with no current member skip the source's failing member dereference when reporting
a fatal branch; this remains an explicit compatibility difference.

Injected native sessions now forward their reporter through single-owner and
parallel verification. Trigger choices precede function/predicate/method results,
member warnings precede their corresponding results, and completed runs emit one
termination event. Reporter failures propagate; warning sinks retain warnings,
including when reporting fails, and simultaneous execution/reporting failures
retain the original typed error inside the combined error. Method initialization
failures still deliver warnings already collected. Real-Z3 checks cover success,
failed proofs, reuse and reporter failures with one/two workers. Native buffered
warnings currently lack source category/position provenance and are emitted as
generic verification warnings; plugin-aware reporter rebinding remains open.

The injected native verifier now exposes the pinned source's static Z3 and cvc5
dependency descriptors in source order, independent of the selected transport.
Its version identifies the native Ferrum package build rather than pretending
to reproduce JVM BuildInfo. This metadata path starts no solver.

Configured AST/PAST provider resets now pass their shared configuration to
reporters after rebuilding plugins, matching the source reset order. StdIO partial
result output follows the latest configuration while retaining its standalone
public setting when no configuration is installed. Configuration failures
propagate. Injected API initialization retains its distinct source path and does
not perform this reset hook; live plugin-manager reporter rebinding remains open.

Decider assumptions and checks now support optional source symbolic scopes,
including nested prover assertions, enabled-only statistics and failed-query
tracking. Model generation uses only the prover assertion scope and leaves the
member's failed query unchanged. Failed solver calls leave their scopes open as
in the source. A real-Z3 integration check covers filtering, empty sequence
assumptions, continuation order, model generation and error scopes. Full-state
record factories also construct joins, implications (including the nullable
ForPerm expression) and conditional expressions. Session attachment and exact
JVM double formatting for statistic deltas remain explicit dependencies; these
hooks do not enable public logging profiles.

The internally gated branch scheduler now also accepts owned predicate-content
actions. It reuses CFG worker transfer/restoration and queue handling, while
predicate joins merge recorded states without CFG consolidation, as in the
source. Focused one/two-worker positive and negative cases submit real predicate
jobs, pass through stdio and linked Z3, and agree with the pinned JVM result.
Evaluator, joined producer/consumer and nonjoined continuations retain their
existing synchronous behavior. The public parallel-branch option remains gated.

Synchronous expression, function, unfold/apply and impure joins now open a
full-state JoiningRecord before entering their local solver scope and close it
at the source continuation boundary, including successful joins with no entries.
Fatal results and execution errors leave the scope open. A focused real-Z3 check
covers original-state capture and the empty/error boundaries. Parallel join
logging and remaining rule events are still separate from these optional hooks.

Plugin-aware, StdIO, CSV and Polling reporters now bind ordered shared entity
mapping views during configured provider reset and injected API factory setup.
The built-in Refute, PredicateInstance and Termination views reuse their existing
mapping algorithms and immutable mapping data; other known plugins, including
Silicon TryBlock, retain identity mapping. Callbacks run outside reporter locks,
so supported concurrent and reentrant entity mapping needs no mutable-manager
lock. Polling still enqueues and forwards under its queue lock. Only entity
success/failure events are mapped; overall and branch messages retain source
behavior. Provider plugin disabling preserves the source's earlier reporter
binding. Custom mutable plugins must supply an explicit concurrent shared view
or receive an unsupported error when bound to a plugin-aware reporter; plain
reporters remain usable. The older opaque-callback API initializer still cannot
bind an inaccessible manager, and broad transformed-failure parity remains open.

The injected Refute regression checks mapped entity and final outcomes with
one/two workers: refuting false succeeds and refuting true reports the source
refutation failure. It passes with both stdio and linked Z3.

Evaluator implication and conditional-expression records now open before operand
evaluation and close on the successful continuation. ForPerm records retain the
source null expression, capture state before local definitions, and close after
quantifier construction before processing remaining alternatives. Disabled
logging remains inactive; active hooks use the full-state factory. These scopes
complement the synchronous join records without enabling a reporting profile.

Method CFG completion now owns its Method and retains the source order of
post-state preparation and postcondition consumption. Statement sequences own
their remaining statements and resume index, cloning the same next frame for
each continuation invocation. Normal CFG blocks own their successor context and
query outgoing edges from the resulting state after statements finish. These
are used in ordinary synchronous execution and preserve fallback, branch and
block-completion order. Their enclosing CFG/loop/retry/production/consumption
continuations still borrow outer callbacks; nonjoined offloading stays disabled
until the complete continuation chain can move together.

PollingReporter now uses an owner-thread reentrant monitor for reporting and
queue access, matching the JVM synchronized methods. Queue storage locks end
before pass-through callbacks, while the monitor preserves ordering against
other threads. Nested reporting and queue access on the same thread therefore
complete, and RAII releases the monitor after callback errors or unwinding.
Already queued messages remain available. Focused checks cover reentry,
serialization and error/panic recovery.

Impure production and consumption conditionals now capture their source record
and close it in each successful branch before the collector or continuation.
False implications retain the source empty/unit snapshot ordering. Execution
records now retain each statement and its original state before execution-heap
selection, closing after reserve-heap restoration and before the continuation.
Nested statement scope IDs remain distinct. These optional hooks preserve the
disabled path and leave public reporting profiles gated pending the remaining
branch, retry, consolidation and lifecycle integration.

CFG edge execution now owns destination, incoming-edge kind, join context and
path identity. Ordered edge folds and post-join continuation context are owned
as well; target lookup, conditional flag restoration, lazy path IDs and source
combine/error order remain unchanged. The outer continuation is still borrowed,
so these frames continue to execute synchronously while loop and rule frames
are converted.

Loop-head continuations now own the ordered condition checks, outgoing edges,
join context and path identity. Condition checks retain their separate local
solver scopes and fatal-result handling before edge execution. An owned
loop-phase frame carries recorded states, paths, declarations and statements
through invariant establishment and replay. The outer continuation and local
cleanup callbacks remain borrowed, so loop execution remains synchronous.

Default heap merging and consolidation now emit the source comment, single-merge
and fixed-point round scopes, retaining the original state and path conditions.
Minimal and mask paths keep their source behavior. Retry logging captures the
post-consolidation state and closes only when the retry reaches its continuation,
before restoring retry flags. Native reporting profiles remain gated pending
run-root attachment and remaining record coverage.

Concrete AST and reformatter providers now execute the source frontend sequence:
copyright, configuration and early exits, requested dependencies, reset, selected
phases and finish reporting. The AST provider includes semantic, translation and
consistency phases; reformatting remains parse-only. Source plugin resolution
failures emit exception events and stop before phases. Reporter failures retain
the original plugin error. Native exception stack provenance and the generic
missing-dependency catch remain incomplete; no stack trace is synthesized.

Method postcondition well-formedness checks now retain their source logging
record: the initialized method state before debug setup, the postcondition
identities and current path conditions. The record opens after the empty
post-check heap is selected and closes only in the production continuation.

AST provider plugin failures now carry an actual native Rust backtrace captured
at missing-plugin error construction. StdIo and CSV exception reporting can
consume this payload; opaque resolver failures are labeled at their resolver
boundary. Direct reset keeps its existing typed error contract.

Method calls now emit their call record and Parameters, Precondition and
Postcondition subscopes. Each closes at its source success continuation, before
restoring caller state and completing the outer statement. Disabled logging
retains the previous execution path; advanced profiles remain gated.

Native debug heap services now connect intermediate snapshots, old labels and
statement key-heap start/finish/label recording. Statement entry preserves the
source evaluation-heap lookup even with debugging disabled: mask reserve-heap
merges can create aliases and solver assumptions. The unused PCS copy is skipped
when debugging is disabled. Heap probes and actual recording retain source
order, including separate evaluations during key-heap completion. Full debugging
remains gated pending non-statement lifecycle and expression reconstruction.

Synchronous branch exploration now records feasibility-selected arms, nested
ordered edge folds and conditional-edge scopes with distinct IDs. Branch points
end after normal results, including fatal verification results; service errors
retain the source open-scope behavior. Conditional-edge records enclose Out-edge
heap restoration and close in the branch continuation. Parallel logging and
public profile activation remain pending.

Native execution-trace assembly retains ordered member log handles and actual
caller-supplied domain/postcondition terms. Rendering is deferred until the
receiving reporter renders the message, so retained logs preserve subsequent
record updates. Unsupported native record/term rendering returns a reporting
error instead of panicking. Top-level axiom collection and runtime activation
remain separate integration steps.

Native decider logging now follows the active member when an explicit statistics
formatter is installed. Replacing a member rebinds the decider; replacing the
root or resetting the context clears stale attachments. Closing a member retains
the source attachment until the next member. Exact JVM floating-point formatting
and automatic public profile setup remain separate requirements.

Method and loop debug heap lifecycles now connect precondition, postcondition,
invariant and Out-edge merge records. Method completion retains the source
unconditional final-heap lookup even while debug recording is disabled. Loop
consumption captures one finished leftover record for all replayed phases, and
key heaps finish only at source success continuations. Debug-enabled execution
remains gated and has not received an end-to-end compatibility pass.

An explicitly enabled internal trace now snapshots the actual ordered domain
contributor axioms and main function-unit postconditions after member work,
then reports before termination. Traced method/CFG workers must carry the same
run-owned root and an owner-local record factory; missing or mismatched setup
fails before execution. The default parallel factory still lacks this setup,
so public trace profiles remain gated. Repeated native runs currently report
only current-run postconditions, unlike the pinned source reset behavior.

Quantified permission removal now emits its source full-state comment scope,
including the source open scope on read-only early return. Complementary CFG
edges also retain the source conditional record without an invented close.
Active rule/supporter record sites have now been audited against the pinned
source; public profile setup and parallel branch log transfer remain incomplete.

Fresh native locals now retain parser type handles and construct versioned
debug expressions when the decider debug setting is explicitly injected.
Statement/loop and method locals share the source conversion, including typed
domain-function argument metadata and Unknown fallback when metadata lacks a
source type. Malformed domain argument nodes fail explicitly. Public debug
configuration remains gated while other expression families are incomplete.

Wildcard permissions now use the source fresh `$k` identifier and register
permission parser types and versioned variables when decider debugging is
injected. Their positive-permission assumption carries the source internal
debug description. An actual wildcard evaluation exercises this path through
a test-only evaluator switch; production debug activation remains gated.

The native backend now retains an explicitly supplied logger owner across resets
and attaches its shared root to main and method-worker contexts with local record
factories. Final stop joins workers before closing the logger and retains both
solver and logger cleanup errors. An outstanding internal pool borrow keeps the
context alive for a later stop retry. Real Z3 checks cover one/two workers, reset,
trace-report failure and retry; public profile construction and timeout traces
remain incomplete.

SSA assignments now record their source defining equations rather than ordinary
assumptions, preserving them for definition-only replay. Injected debug execution
retains the original and rewritten equality and typed/versioned SSA, quantified
and ForPerm locals. The actual assignment fixture checks replay membership; the
quantifier path still reports its missing auxiliary debug service explicitly.
Production debugging remains disabled pending the remaining services.

Timeout traces now preserve the actual member log handles and use the two empty
axiom lists explicitly specified by Silicon's timeout handler. Native cleanup
joins workers and closes the logger before reporting, retains the owner for
subsequent verification, and propagates reporter failures. Interrupted solver
shutdown errors remain warnings once workers are quiescent and logger close
succeeds. Tests cover one/two workers, timeout followed by success, rejected
reports, and outstanding-pool cleanup; public trace configuration stays gated.

Solver-statistics deltas now parse Java-style decimal inputs, including surrounding
ASCII control/space characters, decimal suffixes and Java special-value spellings.
Rust-only infinity/NaN spellings no longer produce misleading deltas. Hexadecimal
float parsing and exact JVM double output remain explicit compatibility gaps;
the output formatter is still supplied separately.

Quantifier debug services now reconstruct guarded auxiliary records with their
original/rewritten expressions, bound variables and AST/term triggers. Global
and non-global assumptions retain source grouping, comments and order. A real
quantifier evaluation now succeeds with the injected debug settings; absent
required debug payloads still fail explicitly. Other debug services remain gated.

Direct native AST clients can now supply a reporter through
`Session::new_with_reporter`. It uses the existing owner-thread startup and
warning sink and delivers member/termination events through the same runtime
as the injected frontend. One/two-worker checks cover successful delivery,
reporter failure and continued rejection of unconnected advanced profiles.

Trace and state diagnostics now render predicate lookups, permission lookups,
triggers, macro hints and distinct sets whose concrete Scala collection classes
are absent from the Rust model. These diagnostic paths use canonical native
`Seq(...)`/`Set(...)` notation. Strict counterexample and debug-heap rendering
remain unchanged. Custom value-based log filters use the displayed native form;
the output difference is recorded in differences.md.

The concrete parse-AST provider now executes preparation, configured reset,
parsing and semantic analysis before its existing finish/reporting hooks. It
reports phase warnings and overall results and preserves captured plugin setup
exceptions. Focused checks cover success, semantic failure and missing plugins;
this provider does not invoke the backend.

Native branch services now pass source and rewritten guards through a shared
decider adapter, including both feasible branch polarities and scoped worker
paths. Let definitions retain their grouped equality records, and existential
precondition assumptions retain their forall expressions. Focused real-Z3
checks exercise these expression paths, replay definitions and missing-payload
errors. Production debug configuration remains disabled.

A supplied native statistics formatter now emits round-tripping Rust decimals,
preserves signed zero and uses Java's NaN/Infinity spellings. This removes the
need for a JVM-dependent formatting implementation in native reporting setup.
Finite digit/exponent spelling can differ from Java 17; exact-format injection
remains available and integer-delta handling is unchanged.

Owned nonjoined CFG actions now execute through explicit method-postcondition or
standalone-success terminals, while callbacks created on the executing worker
remain local. The internal scheduler carries owned state and solver snapshots,
drains submitted else jobs after execution/reporting errors, and preserves typed
terminal errors. Actual Z3 regressions cover nested branches, permission loss,
postcondition failures, two fatal branches and forced foreign-worker restoration.
The public option stays gated while loop/nested-wait isolation and remaining
continuation boundaries are completed; see [continuations.md](continuations.md).

Owned CFG terminals now propagate through loop-body replay and loop exit paths,
while invariant collectors and local phase cleanup stay on the waiting caller.
Real Z3 checks exercise body-only and exit-only branches with one and two workers.
Cancellation checks retain the typed error, drain the submitted else, and restore
parent solver depth/options. Joined CFG/predicate scheduling falls back to the
synchronous path for active logging, packaging and extended exhale. Nonjoined
producer/consumer caller frames remain the next continuation boundary.

Direct CFG inhale statements now carry owned caller tails through conditional and
implication production. Jobs retain split snapshots, projected assertion suffixes
and errors, then complete inhale saturation, statement cleanup and the remaining
CFG through method postconditions. CFG and producer jobs share scheduling,
restoration and error draining. Real Z3 checks confirm producer jobs run with one
and two workers and match pinned JVM outcomes for permission tails, nested
conjunction/Let fallback and failing postconditions. Consumer and additional
caller frames remain gated work.

Owned exhale and ordinary assert continuations now carry conjunct/heap completion
and exact retry attempts through worker branches. Per-attempt success signals
prevent downstream failures from retrying successful consumption; synchronous
retry keeps its original local Boolean without shared allocation. Actual Z3
checks cover nested permission branches, assertion heap restoration, missing
permissions and downstream failure with one and two workers, matching the pinned
JVM. Method contract and other caller ownership remain separate pending work.

Method postconditions now use an explicit owned success terminal, distinct from
statement cleanup. The owned entry is selected only by complete_method_cfg and
preserves per-postcondition error attribution. Actual Z3 checks with one and two
workers prove conditional ensures jobs execute even with empty bodies and retain
an else-only missing-permission error, matching the pinned JVM.

Nested Seqn/TryBlock and loop-head statement continuations now own their enclosing
finish and successor frames. TryBlock success is recorded before downstream work;
failure fallback retains the original heap. Producer/consumer Let bodies and
success-only rule closes are explicit frames. Real Z3 constructed CFG tests cover
these paths and fallback heap restoration with one and two workers; a retained
resource scaffold supplies the existing QP preamble requirements. Rule-only Let
tests confirm actual jobs, and disabled scheduling avoids statement-tail clones.
