# Deterministic native preamble emission

The sort-order bug identified during the [saturation comparison](performance-saturation.md)
is fixed. All four validation inputs now produce byte-identical complete SMT
command and response streams across three fresh processes each. All twelve
captures retain their expected verification outcome and replay exactly through
Z3. This is a reproducibility check, not a speedup measurement.

## Cause and fix

`native_preamble.rs` iterated a randomized ground-type `HashSet` directly when
assembling domain declarations, functions and axioms. Sequence, set and multiset
instances were sorted only by nesting depth, leaving equal-depth instances in
hash order. Map instances were emitted directly from another hash set.

Domain instances now follow program declaration order, with structural ordering
among instantiations of each generic domain. Collection instances are ordered by
nesting depth and a structural type key; depth includes nested maps. The key
sorts generic substitutions and backend interpretations explicitly, avoiding
randomized map debug output or ambiguous printed sort names. Set membership and
the ground-type closure are unchanged. Within each instance, function and axiom
source order is preserved. Saturation defaults are unchanged.

Fresh repetitions then exposed a second source of nondeterminism: call-graph
analysis also used a `HashSet` for successor components. When one component
released several callees, hash iteration changed their topological heights and
therefore function verification and declaration order. Successors now use an
insertion-ordered set, preserving call discovery order while retaining edge
deduplication and the same dependency constraints. A regression repeats a graph
with branching dependencies, a shared callee, duplicate edges and a recursive
component 128 times.

The new unit regression reparses and analyzes a mixed domain/collection fixture
sixteen times, comparing serialized sort/function declarations and axioms. It
also checks the restricted generic-domain path. It covers multiple generic
parameters, unique functions, all four collection families, equal-depth ties,
nested maps and mixed collection nesting.

## Validation

The old `afdf10c` binary reproduced three distinct sort orders on three fresh
runs of the small mixed fixture. With the fix, each row below has three complete
captures with identical raw commands, canonical commands, sort declarations,
responses and the displayed solver-work counts:

| Input | Outcome | Sort declarations | SMT commands | Quantifier instantiations |
| --- | --- | ---: | ---: | ---: |
| `mut_element_nested_pass` | Verified | 48 | 14,032 | 181,264 |
| `mut_element_array_pass` | Verified | 50 | 6,678 | 1,337 |
| `mut_element_array_wrong` | Expected failure | 50 | 6,976 | 1,609 |
| Mixed preamble fixture | Verified | 22 | 761 | 4 |

The negative control retains `exhale.failed:assertion.false` at
`mut_element_array_wrong.vpr@1786.10--1786.82`. All captured response prefixes
match their independent fixed-stream Z3 replay; all cleanup and artifact-hash
checks pass. Counters above come from those replays, not wall-time subtraction.

These runs reuse the saturation experiment's input bytes, Z3 4.16 binary,
persist-before-forward recorder, resource limits, cache policy and CPU affinity.
They use one worker, branch parallelism off, base saturation 100 ms and the
unchanged `[1,0.5,0.4,0,0]` weights. They establish fresh-process reproducibility
for these inputs; they do not assert deterministic parallel scheduling or choose
a faster saturation policy.

`cargo test -p ferrum-silver -p ferrum-silicon --lib -- --test-threads=2` passes
438 Silver and 296 Silicon tests, with 43 Silicon tests ignored. The default
capture driver builds, and
`cargo check --workspace --all-targets --features native-z3` passes. The changed
Rust files pass rustfmt and the patch passes `git diff --check`.

The [machine record](preamble-determinism.json) contains the frozen spec, schedule,
all per-run stream hashes and counters, baseline sort sequences, build/source
hashes and complete local evidence inventory. Raw captures, replay outputs,
validation script and build logs remain in
`/tmp/ferrum-deterministic-preamble-validation-complete`. The sort-only validation
that exposed the later function-order difference remains recorded separately in
the machine report; its proof and sort checks passed, but its full-stream
determinism gate failed. Earlier saturation measurements
remain historical; the controlled policy comparison can now be repeated against
stable emission before considering default changes.
