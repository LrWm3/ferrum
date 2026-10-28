# Port status and checks

The description pass covered all 336 mapped Silver/Silicon source and test files.
The Cargo workspace now has 404 mapped and assembly modules. `described` files
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
native runner regressions also pass. Full trigger rewriting and advanced reporting remain incomplete. No comparative speed improvement
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
parallelism, active-query cancellation and advanced profiles remain incomplete;
standalone CFG-only contributor analysis has upstream TODOs. No parallel speedup
has been measured against upstream.

Source consolidation modes, quantified chunk ordering and the distinct
`disableCaches` / `disableValueMapCaching` policies now reach the native context.
Method inclusion/exclusion uses whole-name matching in both sequential and pooled
execution; functions and predicates still run independently of method selection.
A 126-case matrix passes through both transports. The source minimal consolidation
mode remains incomplete for some aliased fractional permissions. Native method
filters currently accept a shared subset of Java/Rust regular expressions and
reject unsupported syntax explicitly.
`disableISCTriggers` now connects the source no-trigger rules and preambles.
Ten positive/negative field, predicate and wand cases pass through both transports.
Three pinned template-name defects are corrected during instantiation, as recorded
in [differences.md](differences.md).

The opt-in SIF plugin now connects paired domain/permission values, relational
predicate helpers, optimized loops and AST return/termination control. Source
`old` assertions and inactive `inhale false` guards retain their transformed
obligations. A frozen 66-case CLI suite and ten constructed-program cases passed
through both solver transports, along with positive/negative ForPerm probes.
AST break/continue, exception, try/catch/else/finally and inlined-call control
now connect the source activation flags and restoration order. A further 35-case
constructed-program matrix passes on both transports, including failing assertions
after control transfers. Broader relational compatibility remains unproved.

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
Logging and richer runtime reporting remain unfinished. Dynamic options remain
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
