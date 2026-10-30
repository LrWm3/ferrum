# Separate method solver with one worker

The subsequent [four-way interaction test](performance-method-saturation.md)
found a nested-case timeout when this mode was combined with older saturation
weights. Its stopped schedule and prefix diagnosis are separate from the
current-saturation observations below.

The one-worker experiment reproduces the nested workload's solver-work reduction:
**23.9% fewer quantifier instantiations and 19.7% less Z3 resource work**. Both
repeats produced the same streams and counters within each mode. Untraced backend
timings were 22.4–27.0% lower, but unchanged frontend timings also varied, so this
small shared-host experiment does not establish an exact causal latency gain.

The new opt-in switch is committed as `dd263e8`:

```text
--numberOfParallelVerifiers=1 --parallelizeBranches=false --separateMethodSolver
```

This selects Ferrum's existing worker-pool lifecycle. Functions and predicates
use the owner solver; methods share one separate worker solver for the request.
It does not create a new solver for every method. The default remains the
retained single-context path. The small array case incurred more solver work and
did not establish a consistent timing improvement.

## Fixed comparison

Both modes use the same rebuilt binary at `dd263e8`, including the earlier term
hash cache. Only `--separateMethodSolver=false/true` changes. Both set the worker
count to one, with branches off, internal caches on, modern saturation weights
`[1,0.5,0.4,0,0]`, the existing development build profile, the same pinned Z3 and
input bytes, and affinity `0,1,2,3`. The separate mode has two SMT sessions in
total: owner and worker. All reported solver-work totals include both.

The fixed schedule was:

1. Capture the wrong-array and passing-array controls in both modes.
2. Capture the nested case in retained, separate, separate, retained order.
3. Run four fresh untraced phase sessions per positive case in the same ABBA order.

Program/outer/offline limits were 60/90/45 seconds. There were eight captures,
twelve solver-stream replays and eight untraced timing sessions. Everything
completed in **312.4 seconds**, excluding compilation and the focused tests.
No retry, timeout, invalid outcome, cleanup failure or artifact mutation occurred.

## Solver work

| Case | Retained checks / separate checks | Retained instantiations | Separate instantiations | Retained resources | Separate resources |
| --- | ---: | ---: | ---: | ---: | ---: |
| Nested pass, each repeat | 1,111 / 1,112 | 181,264 | 137,899 | 18,540,052 | 14,890,364 |
| Array pass | 406 / 407 | 1,337 | 1,280 | 613,017 | 819,033 |
| Array wrong | 475 / 476 | 1,609 | 1,612 | 774,833 | 982,583 |

The nested case retained the earlier two-worker diagnostic's reduction with just
one method worker. Thus additional method workers are not required for this
effect. Selecting the worker path still changes solver history, the worker
preamble and fresh-symbol names together; this does not isolate history alone.

The separate path emits and saturates a second preamble. On the passing array
case, total resource work increased **33.6%** despite 4.3% fewer instantiations;
on the failing array control it increased **26.8%**. Instantiation count alone
therefore cannot rank overall cost across these cases.

Nested fixed-stream solver replay CPU, summed across owner and worker, was
**9.69 / 9.04 seconds** and **13.16 / 6.69 seconds** for retained/separate pairs.
Both favor the separate path, but their differing ratios also show timing noise.
Replay CPU is measured separately and must not be subtracted from live elapsed
time to infer exclusive native execution.

## Elapsed time and its limits

The untraced stage uses the timed driver with the real Z3 executable, without
a trace relay or prover log. `session_verify_inclusive` measures backend
verification including solver time; parsing and type checking are separate.
Paired observations below are displayed retained versus separate, reversing
the final ABBA pair for comparison.

| Case / interval | Retained seconds | Separate seconds | Separate/retained ratios |
| --- | --- | --- | --- |
| Nested backend | 11.973, 15.171 | 8.738, 11.780 | 0.730, 0.776 |
| Nested whole session | 34.172, 37.919 | 24.956, 29.230 | 0.730, 0.771 |
| Array backend | 1.001, 0.740 | 0.772, 0.773 | 0.771, 1.045 |
| Array whole session | 2.434, 1.820 | 1.824, 1.824 | 0.749, 1.002 |

Nested backend observations improved **27.0% and 22.4%**. Whole-session
observations improved 27.0% and 22.9%, but semantic analysis, which this switch
does not change, also dropped from **17.56 / 17.35 seconds** to **12.46 / 12.80
seconds** in the corresponding pairs. Host variation therefore contributed to
the observed whole-session differences and may affect backend times too.

Separate-mode session startup took 17–18 ms on the nested case, versus 11–12 ms
in retained mode. This small interval is not the entire handoff/preamble cost;
work also occurs during verification. Array timings moved in opposite directions
between pairs. The separately instrumented nested captures likewise had mixed
elapsed ratios, **1.162 and 0.929**, while preserving identical work counters
within each mode. The report retains those observations rather than pooling them
with untraced timing or excluding the unfavorable pair.

## Validation and conclusion

The seven selected configuration-related tests pass. A real-Z3 injected-AST test
runs six successive programs in each mode: valid function axioms, a false method
assertion, an invalid function postcondition, a changed function definition,
another expected failure and successful recovery. Both modes agree on success,
error IDs and source positions, and support repeated shutdown. The workspace
all-targets check with `native-z3` also passes; linked-Z3 runtime testing was not
repeated in this experiment.

All generated-input captures have the expected outcomes. The wrong-array control
still reports `exhale.failed:assertion.false` at
`mut_element_array_wrong.vpr@1786.10--1786.82`. Every retained-mode stream matches
the earlier baseline input/output hashes and work counts. Nested repetitions
match exact input/output hashes and work counters within each mode; every stream
replays all original responses, and all supervisors report complete cleanup.

The separate method-solver path is a useful opt-in candidate for hard workloads.
The reproducible reduction in nested solver work supports the lifecycle
hypothesis, while the small-case overhead argues against changing the global
default from this experiment. These are generated Viper workloads plus focused
injected-AST tests, not a fresh full Rust stdlib or pinned-Silicon matrix.

The [machine report](performance-method-solver.json) retains the frozen spec,
commands and hashes, all capture and timing observations, paired ratios, trace
audits, test records and runner source. Raw artifacts are under
`/tmp/ferrum-method-solver-235b245`. The preceding
[term-cache investigation](performance-term-cache.md) contains the two-worker
diagnostic that motivated this controlled follow-up.
