# Ferrum: direct Rust port of Silver and Silicon

## Objective and working approach

Build a native Rust implementation of the existing Silver and Silicon code,
preserving their organization, verification algorithms, and behavior as closely
as practical. Ferrum will expose a Rust library and a command-line executable,
and will continue to use an existing SMT solver, initially Z3.

The implementation sequence is:

1. Inventory the upstream code and establish Rust types and crate boundaries.
2. Translate each component into Rust, using compilation and structural checks
   as the main feedback loop.
3. Connect the translated components into the complete verification pipeline.
4. Run a broader compatibility, correctness, and performance testing pass.
5. Optimize or reorganize only after the port has a useful compatibility baseline.

This is a component-by-component port of the existing implementation. The first
implementation should retain its rules, representations, and control flow rather
than introduce a smaller verification algorithm. Difficult features remain on the
porting list even when their implementations arrive later in the sequence.

This document is the plan only. Writing it does not start the implementation.

## Upstream baseline and scope

Use these checked-out revisions as the initial reference:

| Repository | Revision | Role |
| --- | --- | --- |
| [Silver](https://github.com/viperproject/silver) | `c4f54b84703a04434b03e97bfea87dbd09870fd2` | Language, AST, frontend, transformations, plugins, verification interfaces |
| [Silicon](https://github.com/viperproject/silicon) | `ff386aec4664231dc6f2cb56d8d35f1623088363` | Symbolic execution, permission reasoning, SMT encoding, verification orchestration |
| [Helium](https://github.com/viperproject/helium) | `877a3fa3103fb2461a28ef635af81e940d5662db` | Optional reference for Rust implementation techniques |

Silicon's checked-out Silver submodule matches the Silver revision above. Keep
that pairing fixed while porting. Upstream updates should be separate, deliberate
changes so behavioral differences can be traced to a particular baseline.

The sibling checkouts in `../silver`, `../silicon`, and `../helium` are available
for development. Record source URLs and revisions in a future
`porting/sources.toml`; provide a bootstrap command for obtaining the same
references on another machine. Ferrum must not require these local absolute
paths to build or run.

The port includes executable Silver and Silicon code, solver resources, built-in
axiomatizations, configuration behavior, diagnostics, plugin transformations,
and the machinery needed to connect them. Account separately for upstream test
harnesses, build tools, examples, obsolete files, and platform adapters.

Helium is useful reference material, but its verifier is not the semantic baseline
for this project. Reusing a component requires checking that it implements the
corresponding upstream behavior. Do not substitute Helium's verification pipeline
for the requested Silicon port.

The initial project does not rewrite Z3, Carbon, Prusti's ownership analysis, or
the separate ViperServer/IDE projects. JVM-specific runtime mechanisms will have
native Rust replacements. The completed Ferrum execution path must not depend
on Java or JNI; the Scala tools remain available as comparison executables.

## Cargo workspace

Start with three packages, following the existing major dependency boundary:

| Package | Targets | Responsibility |
| --- | --- | --- |
| `ferrum-silver` | Library | Port of Silver's language infrastructure and verification interfaces |
| `ferrum-silicon` | Library | Port of Silicon, including symbolic state, rules, solver interaction, and worker management |
| `ferrum` | Library and binary | Small public facade, configuration/CLI entry point, and pipeline assembly |

`ferrum` is the root Cargo package and the workspace root. The initial layout is:

```text
Cargo.toml
Cargo.lock
rust-toolchain.toml
AGENTS.md
PLAN.md
src/
  lib.rs
  main.rs
crates/
  ferrum-silver/
    Cargo.toml
    src/
      ast/
      parser/
      cfg/
      frontend/
      plugin/
      components/
      verifier/
      reporter/
      logger/
      utility/
  ferrum-silicon/
    Cargo.toml
    src/
      state/
      interfaces/
      decider/
      resources/
      rules/
      supporters/
      verifier/
      reporting/
      logger/
      debugger/
      extensions/
      common/
      config.rs
    resources/
porting/
  sources.toml
  modules.toml
  differences.md
tools/
tests/
```

The dependency direction is:

```text
ferrum -> ferrum-silver
ferrum -> ferrum-silicon -> ferrum-silver
```

Keep closely connected modules together. For example, Silicon's state, decider,
rule, and supporter types refer to one another; splitting each into a crate at
the outset would force unnecessary interface changes. Its `common/` sources
also reference Silver, so they initially remain inside `ferrum-silicon`.

Extract additional crates only when a concrete dependency boundary justifies
them. Possible later extractions include a dependency-free common library, an
SMT transport library, or a procedural-macro crate for repetitive AST plumbing.
An extraction must preserve behavior and must not create a dependency cycle.
Do not create empty utility crates merely to match every upstream directory.

Pin a Rust toolchain and dependency lockfile when the workspace is created. Keep
the verifier crates independent of `rustc_private`; Prusti-specific conversion
belongs in an adapter on the Prusti side.

## Translation rules

### Preserve structure and behavior

- Keep recognizable upstream module, type, and function names, using Rust naming
  conventions where needed. Split oversized files along existing conceptual
  boundaries and record the correspondence.
- Preserve rule dispatch, branch order, retries, state consolidation, solver
  scoping, and configuration-controlled alternatives.
- Preserve transformations, axiom generation, trigger selection, and the order
  of logically significant operations. Avoid new simplifications during the port.
- Carry source positions, annotations, error transformations, and diagnostic
  categories through the same stages as upstream.
- Preserve upstream license headers and attribution in translated code, and
  retain the notices accompanying copied resources.
- Record unavoidable changes in `porting/differences.md`, including their source
  location and reason. Keep fixes to upstream behavior separate from translation.

### Adapt Scala mechanisms deliberately

| Scala mechanism | Initial Rust approach |
| --- | --- |
| Case classes and sealed hierarchies | Structs and enums with corresponding fields and variants |
| Traits, mixins, and singleton components | Traits and explicitly owned components, with contexts passed where upstream used global access |
| Immutable trees and shared terms | Shared immutable handles or typed arena handles, preserving identity and equality contracts |
| Immutable state updates and `copy` | Explicit state updates/clones that preserve independent branch state |
| Mutable worker-local structures | Worker-owned mutable state; use interior mutability only where the source requires shared mutation |
| `Option`, exceptions, and verification results | Explicit options and distinct result/error variants matching the source outcomes |
| `BigInt` and exact permission arithmetic | Arbitrary-precision integer and rational representations |
| Reflection-driven AST reconstruction | Explicit visitors, reconstruction functions, or narrowly scoped generated implementations |
| Flyweight macros and term factories | Explicit interning/factory code preserving the source's sharing and equality assumptions |
| Continuations and higher-order rule composition | Explicit continuation interfaces or closures preserving invocation order and failure propagation |
| Futures, executors, and process pools | Rust threads/channels and owned solver processes with matching lifecycle behavior |

Before deriving `Eq` or `Hash`, inspect which fields participate upstream. Source
metadata and interned-node identity must not accidentally change cache keys or
term equality. Inspect `flyweight.scala`, `Terms.scala`, and Silver's reflective
rewriter when choosing these representations.

Audit collection semantics at each translation site. Preserve insertion order
where upstream uses ordered collections. Do not globally sort declarations or
substitute randomized iteration for a known order: these changes can alter SMT
behavior. Treat any normalization of upstream unordered iteration as an explicit
recorded difference.

Keep branch-local heaps, stores, old states, and path conditions independent.
Using a shared mutable object to avoid a Rust ownership error must not make an
update in one branch visible in another. Prefer a straightforward faithful clone
over inventing a new state-sharing algorithm during the initial port.

Preserve lazy evaluation where it has observable effects. Preserve arithmetic
semantics, including negative division/remainder and exact permission values;
do not replace mathematical integers with machine integers or permissions with
floating-point approximations.

Use native Rust ecosystem libraries for ordinary CLI, logging, numeric, and
collection support after checking the required semantics. There is no need to
reimplement Scala's standard library or reproduce the JVM's object model.

## Port inventory and completion tracking

Create `porting/modules.toml` when implementation starts. Each source component
gets an entry containing:

- Upstream repository, revision, path, and relevant symbols.
- Destination crate/module and its prerequisites.
- Status: `mapped`, `skeleton`, `ported`, `wired`, or `validated`.
- Any explicit exclusions, remaining code paths, and translation differences.
- The checks performed at the current stage.

Use a file-level entry by default; use symbol-level entries for large files such
as `Terms.scala`, `Evaluator.scala`, and `Executor.scala`. Track resource files and
configuration alternatives as well as the default execution path.

`ported` means the implementation has been translated and compiles. `wired` means
the real caller reaches that implementation. `validated` is reserved for the
broader comparison pass. Neither a compiling skeleton nor a CLI that starts is
evidence that a verification feature is complete.

Temporary placeholders must produce an explicit internal port-incomplete or
unsupported result. They must never return success, discard a proof obligation,
or replace a missing rule with an assumption. Keep them listed in the inventory
and make their presence visible when assembling the pipeline.

Account for every source file. For non-runtime files such as `.bak` files or
obsolete build scaffolding, record why a Rust implementation is unnecessary.
This avoids silently shrinking the project to the easiest features.

## Component map

Paths in the Silver rows are relative to
`silver/src/main/scala/viper/silver/`; Silicon paths are relative to
`silicon/src/main/scala/` unless otherwise stated.

| Source area | Rust destination | What must be carried across |
| --- | --- | --- |
| Silver `ast/` | `ferrum-silver::ast` | Types, expressions, statements, declarations, metadata, positions, pretty printing |
| Silver `ast/utility/` | Corresponding AST utility modules | Consistency checks, substitution, visitors, rewriting, domains, triggers, simplification, chopping |
| Silver `parser/` | `ferrum-silver::parser` | Parse AST, grammar, macros, resolution/type checking, translation, diagnostics |
| Silver `cfg/` | `ferrum-silver::cfg` | CFG representation/generation, dominators, loops, simplification |
| Silver `frontend/`, `components/` | Corresponding Silver modules | Phase sequencing, component lifecycle, frontend and AST-provider interfaces |
| Silver `verifier/`, `reporter/` | Corresponding Silver modules | Results, errors, model parsing, counterexamples, report messages |
| Silver `plugin/` | `ferrum-silver::plugin` | Plugin hooks and bundled transformations, including ADTs, termination, ARP, SIF, refute, smoke, and predicate instances |
| Silicon `state/`, `interfaces/state/` | Corresponding Silicon modules | Terms/sorts, identifiers, stores, heaps, chunks, snapshots, triggers, complete symbolic state |
| Silicon `decider/`, `interfaces/decider/` | Corresponding Silicon modules | Path conditions, solver interface, SMT serialization, preambles, Z3/cvc5 adapters |
| Silicon `resources/` | `ferrum-silicon::resources` | Resource descriptions, properties, quantified/nonquantified property interpretation |
| Silicon `rules/` | `ferrum-silicon::rules` | Evaluation/execution, production/consumption, heap and permission rules, branching, joining, wands, quantified chunks |
| Silicon `supporters/` | `ferrum-silicon::supporters` | Method/function/predicate verification, domain encodings, collections, snapshots, quantified-permission encodings |
| Silicon `verifier/`, `Silicon.scala`, `Config.scala` | Silicon orchestration/config modules | Main and worker verifiers, pool management, options, lifecycle, cancellation |
| Silicon `reporting/`, `logger/`, `debugger/` | Corresponding Silicon modules | Counterexamples, backtranslation, symbolic traces, diagnostics, debugging interfaces |
| Silicon `extensions/` | `ferrum-silicon::extensions` | Conditional permissions and additional syntax/statement handling |
| Silicon `common/src/main/scala/`, `annotation/` | Silicon common modules and term factories | Collection/concurrency helpers and flyweight behavior |
| Silicon `src/main/resources/` | Embedded/versioned Rust resources | SMT preambles, solver settings, collection axioms, old/mask-heap alternatives, notices |

## Implementation sequence

### 1. Freeze references and create the workspace

Create the workspace manifests, toolchain pin, source manifest, port inventory,
and minimal module trees. Establish diagnostic/status types and the public
verification interfaces before filling in their behavior. Add resource-loading
locations and preserve upstream attribution.

Sketch the signatures connecting the Silver frontend, the Silicon verifier,
reporters, and solver processes. Compile their real type relationships early;
the skeleton is not a substitute for porting the implementations.

**Completion:** all packages are workspace members, build/check together, and
every upstream component has an owner and destination in the inventory.

### 2. Port Silver's data model and infrastructure

Port positions, metadata, types, declarations, expressions, statements, and
programs. Then port visitors, reconstruction/substitution, consistency checking,
error transformation, model/result types, reporters, and utilities.

Port the CFG representation and graph algorithms. Preserve the frontend/backend
contracts that Silicon consumes. Use explicit Rust reconstruction where Scala
relied on reflection; retain the same handling of metadata and extra fields.

**Completion:** Silicon can refer to the real Silver types, and visitors,
rewriters, CFG construction, and consistency interfaces compile together.

### 3. Port Silver's frontend and plugins

Translate the parse AST and grammar, macro expansion, name resolution/type
checking, translation to the verification AST, and frontend phase sequencing.
Keep the distinction between the parse AST and verification AST.

Port the plugin hooks and bundled plugin transformations in dependency order.
Keep their configuration and ordering explicit. Where the JVM used dynamic class
loading, use a native registration mechanism for the bundled plugins and record
the API difference; do not claim JVM plugin binary compatibility.

Finish associated formatting, diagnostics, and frontend utility behavior.

**Completion:** a Viper file can reach a checked Silver program, and each bundled
plugin has a translated implementation or a specifically tracked incomplete path.
Complete those paths before declaring the broad port assembled.

### 4. Port Silicon's representations and solver interface

Port terms, sorts, factories/interning, identifiers, chunks, heaps, stores, old
heaps, snapshot maps, symbolic state, and path-condition stacks. Preserve the
fields used by advanced rules, even before those rules are connected.

Port the prover interfaces, SMT-LIB serializer, preamble reader, naming/escaping,
and Z3 stdio adapter. Copy the selected upstream preambles/settings as resources.
Keep push/pop, timeouts, saturation, assertion modes, model retrieval, statistics,
and `sat`/`unsat`/`unknown` handling aligned with upstream.

Z3 stdio is the first connected solver route. Also account for cvc5 stdio and the
upstream Z3 API route. A native API implementation replaces the Java API route
when that route is ported; it can be an optional Cargo feature. Do not alias it
silently to stdio or leave advertised options as no-ops. Keep these routes in the
inventory and broad validation scope.

**Completion:** the state model and solver interfaces compile, resources load,
and a tiny solver handshake with one satisfiable and one unsatisfiable query
works. This is a protocol check, not the broad verifier test pass.

### 5. Port resource encodings and supporting components

Port resource properties and their interpreters; domain and built-in collection
contributors; expression translation; snapshot support; quantifier support;
function encodings/recorders; predicate verification units; and method/CFG
supporters. Include the quantified field/predicate/wand snapshot contributors.

Preserve alternative encodings such as mask heaps and the configured collection
axiomatizations. Keep dependencies between term generation, triggers, and
resource declarations recognizable from the source.

**Completion:** supporters and resource encodings compile against the real
Silver AST, Silicon state, and prover types, with every translation gap listed.

### 6. Port the symbolic execution rules

Port the mutually dependent rule groups using their upstream interfaces:

1. Expression evaluation, statement execution, local binding, and havoc.
2. Resource production/consumption, chunks, permissions, and heap operations.
3. Branching, joining, execution flow, and state consolidation.
4. Predicate folding/unfolding and heap-dependent function handling.
5. Quantified chunks and quantified permissions.
6. Magic-wand packaging/application and snapshot behavior.
7. More-complete exhale, mask-heap rules, retries, and configuration alternatives.

These are porting work packages, not separate mini-verifiers. Keep the existing
continuation/failure structure where possible. Resolve dependency cycles inside
the Silicon crate rather than replacing the rules with a different algorithm.
Shared interfaces may need to be filled in across adjacent groups together.

**Completion:** all intended rule dispatch paths have translated bodies, compile
against the actual supporters/decider, and have no success-producing placeholders.

### 7. Assemble the complete native pipeline

Port the main verifier, worker verifiers, pool manager, lifecycle transitions,
reporting/backtranslation, logging, debugger support, and remaining extensions.
Connect them to the facade and CLI:

```text
Viper source
  -> parse / expand / resolve / typecheck
  -> Silver AST / consistency checks / configured transformations
  -> Silicon preprocessing / domains / functions / CFGs
  -> symbolic execution and permission rules
  -> SMT solver
  -> verification results / diagnostics / counterexamples
```

The native library also accepts a constructed Silver program through the
appropriate AST frontend path. Preserve the validation and transformation stages
required for that entry point; accepting an AST must not bypass required checks.

Use one worker while diagnosing integration problems, then connect the upstream
worker-pool and parallel-branch behavior. One worker is a configuration, not a
permanent removal of concurrency. Keep solver state isolated per upstream worker
and preserve clean startup, reset, cancellation, and shutdown.

Use a single fixed integration smoke set at this point: a valid assertion, an
invalid assertion, and a basic heap/predicate example. It should exercise the
actual pipeline and error propagation without becoming a feature-by-feature
test campaign.

**Completion:** real frontend, transformations, rule engine, solver, and reporting
are connected; the library and executable link/run; advertised paths do not
reach untracked stubs. The port is assembled, but not yet broadly validated.

### 8. Connect Prusti with a thin adapter

Implement a native conversion corresponding to Prusti's existing
`prusti-viper/src/lib.rs::program_to_viper`. Convert the existing VIR program to
Ferrum's Silver AST and preserve position IDs, declarations, generic/domain
information, and error mapping. Keep changes to Prusti's Rust-to-VIR encoding
outside this port.

Make Ferrum a selectable backend, retaining the Scala backend for comparison.
Use the same verification settings and logical program on both paths. A Viper
text-file route can assist initial integration, but the native adapter is the
intended route for Prusti's normal verification path.

Keep the adapter in Prusti so Ferrum's libraries do not depend on Rust compiler
internals. Preserve Prusti's conversion of verification results to diagnostics.
Until the relevant integration code is reached, an unimplemented backend choice
must report that fact explicitly.

**Completion:** a small existing Prusti example reaches Ferrum and returns its
real verification result, and the affected crates build together. The original
backend is still available for the broader comparison pass.

## Checks during the port

Keep this stage focused on implementation and integration. Do not require a new
unit-test suite for each translated class or function, and do not repeatedly run
the entire upstream or Prusti test suite after every logical chunk.

The normal loop is:

```sh
cargo fmt --all --check
cargo check -p <changed-package> --all-targets
cargo check --workspace --all-targets
git diff --check
```

Use the package check while editing and the workspace check before completing a
chunk. After dependency changes, update and commit `Cargo.lock`; use `--locked`
for reproducibility checks once the lockfile is current.

At module/crate integration boundaries, also run:

```sh
cargo build --workspace
cargo test --workspace --no-run
```

The second command is a compile/link check for any existing test targets, not a
request to build a large early test suite. Check enabled optional solver features
explicitly when those implementations are connected. Run Clippy at meaningful
milestones, fixing substantive issues without using stylistic lint suggestions
as a reason to redesign translated algorithms.

Other inexpensive checks are source-to-port inventory review, resource existence
and checksums, option/variant coverage, visible placeholders, and correct error
propagation at connected interfaces. Keep the solver handshake and final fixed
smoke set small. Add an isolated test during translation only when it resolves a
specific ambiguity that code inspection and compilation cannot settle.

Before the broad testing phase, the evidence is that the port compiles, links,
and is assembled. Compilation alone does not establish verification compatibility.

## Broader testing after assembly

Once the pipeline and Prusti adapter are connected, make testing the main task.

### Reference setup

- Build or obtain runnable Scala Silver/Silicon from the pinned revisions and
  record the exact solver executable/version and settings.
- Run both implementations on the same inputs and configurations. Keep result
  caches disabled for comparisons; separate cold starts from reused processes.
- Reuse upstream fixtures and expectations first. Port their harness behavior
  into a Rust/integration runner as needed; do not rewrite every fixture.
- Compare success, verification failure, invalid input, unsupported features,
  timeout, solver `unknown`, and internal errors as distinct outcomes.

### Coverage passes

1. Frontend and AST behavior: parsing, name/type errors, metadata, transformations,
   CFG construction, and configured plugin behavior.
2. Core verification: arithmetic, branches, loops, calls, functions, predicates,
   permissions, and both positive and negative cases.
3. Advanced reasoning: quantified permissions, wand packaging/application,
   snapshots, old states, joins, retries, mask heaps, alternative exhale rules,
   trigger behavior, collections, and counterexample/error backtranslation.
4. Lifecycle and configurations: multiple requests, worker counts, parallel
   branches, cancellation, timeouts, fresh solver state, and enabled solver routes.
5. Prusti integration: the existing regression suites and stdlib cases, including
   mutable/shared references, reborrowing, framing, wrong postconditions, loop
   invariants, arithmetic overflow, and iterator contracts.
6. Targeted mismatch investigation: compare intermediate ASTs/CFGs and SMT traces,
   minimize inputs, and add regressions for concrete translation mistakes.

Classify every mismatch. An input rejected or unsupported by the reference must
not quietly become a successful proof through an omitted Ferrum rule. Also track
new rejections, timeouts, crashes, diagnostic changes, and incomplete features;
matching successful examples alone is insufficient.

Normalize only incidental details in comparisons, such as paths or generated
names where their correspondence is understood. Do not normalize away missing
assertions, reordered solver commands, changed triggers, or different permissions.
Equivalent logical formulas can still have different solver behavior.

The goal of this phase is an explained compatibility report for the pinned
upstream surface and the Prusti integration, with regressions added for found
bugs. Differential agreement is evidence of compatibility, not a formal proof
that either verifier is sound.

### Performance pass

After correctness mismatches are understood, benchmark release builds on the same
machine and inputs. Measure cold and warm operation, CPU and wall time, memory,
solver time, worker counts, and emitted proof/SMT size. Preserve the initial
translated implementation as the baseline for later Rust-specific optimizations.

The existing Prusti measurements suggest substantial work above Z3, but they do
not predict the payoff of this port. Establish Ferrum's own measurements before
changing algorithms, caching policies, solver settings, or representations for
performance.

## Milestones

| Milestone | Required evidence |
| --- | --- |
| M0: Inventory and workspace | Pinned sources, complete component map, compiling crate skeletons |
| M1: Silver port | Real AST/frontend/CFG/plugin implementations compile and connect through Silver interfaces |
| M2: Silicon representations and SMT | State/term/resource interfaces compile; resources load; minimal solver protocol check succeeds |
| M3: Silicon component port | Supporters, rule families, alternatives, reporting, and orchestration have translated implementations |
| M4: Ferrum assembled | Native source/AST-to-result pipeline links/runs, with a small fixed integration smoke set |
| M5: Prusti connected | Thin VIR adapter and selectable native backend build and return real results |
| M6: Broadly validated | Upstream and Prusti comparisons completed for the declared surface; differences explicitly classified |
| M7: Performance baseline | Reproducible release measurements available before optimization work |

Milestones describe completion criteria rather than calendar promises. Track
progress by mapped, ported, wired, and validated components. Revisit remaining
effort after the Silver data model and Silicon term/state/solver interfaces have
exposed the main language-adaptation costs.

## Commit and push workflow

Follow `AGENTS.md`: commit and push completed logical chunks as implementation
progresses. A chunk normally covers one component or a small group of mutually
dependent components needed to keep the workspace compiling.

Use Linux-style subjects such as:

```text
workspace: Add Silver and Silicon crates
silver: Port source positions and type nodes
silver: Port CFG dominator computation
silicon: Port symbolic stores and heaps
silicon: Port the Z3 stdio prover
silicon: Port predicate consumption rules
frontend: Connect the native verification pipeline
prusti: Add the Ferrum backend adapter
tests: Compare quantified permissions with Silicon
```

Each implementation commit should identify the upstream component, important
translation differences, and relevant checks. Update the inventory with the code
so a compiling placeholder is never mistaken for a completed port. Keep broad
test additions and algorithmic optimizations in their appropriate later phases.
