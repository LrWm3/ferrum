# Term hashing and follow-up performance experiments

Ferrum now caches immutable structural term hashes and checks pointer identity
before comparing term structure (`70bc42f`). These restore optimizations already
present in Silicon's `ConditionalFlyweight` implementation at the port target
`ff386aec`, in `state/Terms.scala:516–539`.

The short array workload improved in both measured pairs. The nested workload
did not establish a latency improvement. All four correctness captures retained
byte-identical solver inputs and responses, including the expected failing case.

## What changed

Previously, every structural `Term::hash` traversed its descendants again.
Sharing makes this particularly expensive: a small DAG can have exponentially
many paths to the same child. The new per-node `OnceLock<u64>` computes the
structural fingerprint once and reuses child fingerprints. Hash collisions still
fall through to full equality. The pointer fast path also avoids comparing a
shared subtree against itself.

Flyweight identity remains unchanged. Mutable auxiliary representations do not
participate in identity, and the cache is omitted from debug output. Four new
tests cover shared DAGs, binding order, flyweight hints, forced collisions,
auxiliary-state updates and concurrent initialization. All **300 enabled Silicon
unit tests passed** (43 ignored), as did the workspace/all-targets check with
`native-z3`. The cache adds a 64-bit value and initialization state per node;
overall memory use was not measured.

## Bounded comparison

The baseline runtime was `4bef39a`, with documentation-only HEAD `fd7d4d1`.
Baseline binaries were copied before changing code. Candidate and baseline use
the same existing development build settings, Z3 binary, input bytes and options:
one worker, branches off, internal caches on, modern saturation weights
`[1,0.5,0.4,0,0]`, and CPU affinity `0,1,2,3`. Program/outer/offline limits were
60/90/45 seconds. No run timed out or required retrying.

Four candidate captures were compared against the earlier deterministic baseline
captures. Each preserved the complete SMT input and output hashes, solver-check
count, quantifier-instantiation count and resource counter. Fresh offline replay
reproduced every recorded response. Expected outcomes and process cleanup passed.

| Fixture | Expected outcome | Checks | Quantifier instantiations |
| --- | --- | ---: | ---: |
| `mut_element_array_wrong` | `exhale.failed:assertion.false` at the original position | 475 | 1,609 |
| `mut_element_nested_pass` | Verified | 1,111 | 181,264 |
| `mut_element_array_pass` | Verified | 406 | 1,337 |
| `mixed_preamble` | Verified | 2 | 4 |

The timing stage used four fresh processes per positive case in baseline,
candidate, candidate, baseline order. It used the real solver directly, with no
trace relay or prover log. The backend interval is the timed driver's
`session_verify_inclusive`; it includes Z3 and excludes parsing/type checking.
Paired observations below are shown in matching order, reversing the final ABBA
pair when displaying baseline versus candidate.

| Case / interval | Baseline seconds | Candidate seconds | Candidate/baseline ratios |
| --- | --- | --- | --- |
| Array backend | 0.822, 0.892 | 0.737, 0.748 | 0.896, 0.839 |
| Array whole session | 1.971, 2.020 | 1.870, 1.868 | 0.949, 0.925 |
| Nested backend | 21.377, 11.957 | 18.122, 14.240 | 0.848, 1.191 |
| Nested whole session | 50.137, 27.832 | 38.715, 38.414 | 0.772, 1.380 |

Thus the array backend improved **10.4% and 16.1%**, with whole-session
improvements of **5.1% and 7.5%**. Nested timing moved in opposite directions
between pairs; the unchanged baseline itself varied substantially. These are
two-pair observations on a shared laptop, not a general stdlib speedup claim.
The four captures, replays and eight untraced timing sessions completed in
**214.6 seconds**, excluding compilation and separate profiling.

## Profiling and other opportunities

A separate initial nested phase run spent 12.11 seconds in semantic analysis,
1.73 in translation, 0.61 in parsing and 11.84 in backend verification, out of
27.63 seconds overall. CPU samples highlighted cloning of parser type
substitutions. For example, `translate_expression_with_fields` clones a whole
`PExpression`, including its substitution candidates, but consumes only its kind
and type. `PTypeSubstitution::compose` and `force_substitution` also copy heavily.
Prusti's direct AST adapter bypasses this parsed-Viper frontend, so improving
these copies would chiefly help `.vpr` workflows.

Separate full-run CPU profiles used `cpu-clock:u` at 99 Hz with 65,528-byte DWARF
stacks. Both verified and cleaned up. Neither reported lost samples.

| Sample category | Baseline | Candidate |
| --- | ---: | ---: |
| All user CPU samples | 2,635 | 2,776 |
| Ferrum process | 1,650 | 1,818 |
| Z3 process | 985 | 958 |
| Stack contains parser code | 1,409 | 1,621 |
| Stack contains Silicon code | 242 | 192 |
| Stack contains `Term::hash` | 43 | 2 |

The hashing hotspot largely disappeared in this sample. Stack categories overlap,
may miss inlined/unrecovered frames, and must not be added or treated as exclusive
phase times. These are two diagnostic profiles, not another latency pair; their
whole-session times were 28.56 and 30.27 seconds. Parser work dominates the
Ferrum-process samples here, obscuring backend improvements in whole-file timing.

An earlier diagnostic in this investigation used the unchanged baseline with
**two method workers, branches still off**, selecting the existing worker-pool
path. Across the owner and both worker solvers it performed **137,902 quantifier
instantiations**, versus 181,264 in the single-context path: **23.9% fewer**.
Total resource work fell from 18,540,052 to 15,089,463 (**18.6% fewer**) while
checks rose from 1,111 to 1,113. The captured session verified in 31.02 seconds;
all three streams replayed exactly and cleanup passed.

This supports investigating the method solver's lifecycle. It does not isolate
freshness: worker count, symbol naming, preamble contents and solver contexts all
change together. The next controlled experiment should select the existing
fresh method-solver path with one worker and branches off, then compare proof
outcomes, emitted contexts, total solver work and startup cost before adopting a
different default. The [short saturation experiment](performance-saturation-short.md)
also remains promising: its older weights reduced solver work, but have not
established a reliable end-to-end gain. Neither configuration default changed here.

That follow-up is now recorded in the
[one-worker method-solver experiment](performance-method-solver.md), including
the new opt-in switch, repeated solver counters and the small-case tradeoff.

The [machine report](performance-term-cache.json) contains frozen artifacts,
binary/source hashes, every timing observation, paired ratios, compact trace
audits, profile counts, validation results and runner sources. Raw evidence is
under `/tmp/ferrum-perf-explore-4bef39a`. This investigation adds focused generated
Viper checks, not a new full Rust verification or Silicon compatibility matrix.
