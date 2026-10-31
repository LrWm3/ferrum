# Follow-up of the 15 inconclusive compatibility cases

The old timeouts are not inevitable. A bounded follow-up on Ferrum `2df948c`
and the same pinned Silicon/Silver references found successful proofs, persistent
timeouts, and a concrete proof-completeness difference. It also identified a
second source of nondeterministic SMT emission, outside preamble construction.
No runtime code or defaults changed during this investigation.

The first pass covers all 15 fixture/configuration entries from
[the final broad comparison](compatibility-final.md), representing eight distinct
programs. Current Ferrum verifies three, rejects three with unexpected proof
errors, and times out on nine. Pinned Silicon verifies two and times out on 13.
Unexpected failures are not resolved timeouts or evidence that the programs are
incorrect. In this first paired pass, linked-list append is a conclusive outcome
difference; the other 14 pairs remain inconclusive because one or both sides time
out. Some entries already verified on one side in the historical comparison.

## Fixed first pass

Inputs, reference JAR/classes, Java, Z3 and the old native executable match the
historical hashes. Current Ferrum was built from an immutable archive of
`2df948c9014de33b7baa13599eaf9d5078906b28`, using Rust 1.89 and the unchanged
development profile (the three Ferrum packages use optimization level 1):

```sh
cargo +1.89.0 build --locked --offline --example compatibility_session -j 3
```

The build used its own source directory and target under
`/tmp/ferrum-timeout-triage-2df948c`, with CPU affinity 8–11. References remain
Silicon `ff386aec` and Silver `c4f54b8`, not Prusti's older bundled Silicon.

Each input runs in a fresh process, with internal caches disabled by the existing
compatibility drivers, a 30-second verification budget and 65-second outer
watchdog. Default and mask profiles use one worker with branch parallelism off;
parallel profiles retain two workers and branch parallelism on. Ground permission
summaries and the separate method solver remain off in the first native pass.
Summary-only snapshot triggers use the current enabled default.

Fresh sessions remove the preceding inputs in the historical batches, so changes
from those results cannot all be attributed to code changes. Jobs ran concurrently
on recorded disjoint CPU sets on a shared host; timings are observations, not
controlled speedup estimates. Session wall time includes startup and frontend
work outside the verifier budget.

**T** means verifier timeout, **V** means verified, and **U** means an unexpected
proof rejection. No run reached the outer watchdog.

| ID | Program | Profile | Silicon | Current Ferrum |
| --- | --- | --- | --- | --- |
| 0 | `testTreeWand` | Default | T | T |
| 1 | `testTreeWandE1` | Default | T | T |
| 2 | `graph-marking` | Default | T | U |
| 3 | `arrays_quickselect_rec` | Default | T | V |
| 4 | `arrays_quickselect_rec_index-shifting` | Default | T | T |
| 5 | `linked-list-predicates-with-wands` | Default | V | T |
| 6 | `linked-list-qp-append` | Default | V | U |
| 7 | `graph-marking` | Parallel | T | U |
| 8 | `arrays_quickselect_rec` | Parallel | T | T |
| 9 | `arrays_quickselect_rec_index-shifting` | Parallel | T | T |
| 10 | `linked-list-predicates-with-wands` | Parallel | T | T |
| 11 | `linked-list-predicates` | Parallel | T | V |
| 12 | `arrays_quickselect_rec` | Mask | T | V |
| 13 | `arrays_quickselect_rec_index-shifting` | Mask | T | T |
| 14 | `linked-list-predicates-with-wands` | Mask | T | T |

Several files retain upstream `IgnoreFile` issue annotations; these did not
exclude them. Graph-marking and `testTreeWandE1` contain intentional negative
assertions. Their expected diagnostics would be useful completions; accepting
those assertions would not be a successful fix.

## Linked-list append exposes trigger incompleteness

Pinned Silicon verifies the unchanged append input in a fresh session (34.10
seconds total wall time, including frontend/startup). Current default Ferrum
finishes in 2.00 seconds but reports `fold.failed:assertion.false` at
`linked-list-qp-append.vpr@60.2--60.22`. An untraced repeat and diagnostic capture
reproduce the rejection. The captured reason for the failed proof is
**`(incomplete quantifiers)`**, rather than a satisfying counterexample.

These follow-ups use the same current binary and whole input, with
`--reportReasonUnknown` enabled:

| Snapshot triggers | Method solver | Result | Session wall seconds |
| --- | --- | --- | --- |
| Summary only | Retained | Same unexpected fold failure | 0.81, repeat |
| Older alternatives | Retained | Timeout | 30.19 |
| Summary only | Separate | Same fold failure, incomplete quantifiers | 0.51 |
| Older alternatives | Separate | Verified | 0.71, 0.71 |

The separate-solver on/off comparison and repeated proofs expose a compatibility
problem with selective triggers on this fixture. The earlier Prusti sample did
not cover it. Extending the time budget cannot help this default execution after
Z3 has already returned unknown. Narrowing the optimization or a controlled
fallback merits investigation; neither is implemented or validated here.

The same trigger switch has benefits elsewhere: default quickselect verifies
with summary-only triggers in 8.40 seconds and an untraced repeat in 4.54 seconds.
Older triggers time out at 30 seconds. There is no universal better configuration
established here. Allocation-order variability below is another reason not to
treat these timings as exact causal performance ratios.

## Another SMT ordering bug in allocation

Linked-list-with-wands does not support a trigger-policy speed claim. It times
out in the first current default run, verifies in 5.92 seconds in a later run
with reason reporting, and times out in both fresh diagnostic captures. The old
`afdf10c` executable verifies it in an isolated 12.15-second run despite its
historical timeout. Current older-trigger mode verifies in 4.65 seconds; adding
a separate solver times out. All observations remain recorded.

The two current default captures use identical input bytes and solver settings.
Their first **1,679 SMT commands and corresponding responses match**. The next
four commands contain exactly the same allocation-disjointness formulas in
different orders. At `tmp := new(data, next, head, held, changed)`, the new
reference is constrained to differ from the same four existing references,
emitted in different permutations. One run later stalls at command 3546, the
other at command 4516. Neither captured prefix contains snapshot-summary or
permission-summary axioms. Both runs time out.

The implementation iterates three randomized Rust `HashSet`s directly in
[`compute_reference_disjointnesses`](../crates/ferrum-silicon/src/state/utils.rs#L53).
The executor assumes their output in order. This is a concrete SMT emission bug,
distinct from the repaired preamble order. An ordered collection following the
existing store/heap traversal is a candidate repair; formula membership,
deduplication and fresh-process streams need checks. These captures establish
the ordering bug but do not isolate its contribution to wall-time variability
in the separate untraced runs.

## Graph-marking and larger-budget probes

In the diagnostic old-Ferrum graph run, 152 solver checks receive responses
before the final unanswered check. Earlier response waits sum to about 0.226
seconds. The last check is sent 1.36 seconds after solver startup and stalls
until the 30-second verifier timeout. It tries to establish `trav_rec`'s
quantified postcondition at line 30: previously marked nodes remain marked.
Its active `rlimit` is zero, so there is no individual resource bound. Most of
this run's budget is spent in one solver query.

Current summary-only triggers finish graph-marking quickly but return errors
for that postcondition and the positive client's assertion at line 67, in
addition to the intentional negative at line 85. These extra failures do not
resolve the fixture. Older triggers on the current binary time out.

Three additional source runs set `--assertTimeout=1000` on graph-marking,
`testTreeWandE1`, and default quickselect. All still time out at 30 seconds.
Under the unchanged resource-bound policy, this setting corresponds to 10 million
Z3 resource units per assertion, **not a one-second wall-clock cap**. This does
not establish that all per-query budgeting policies are ineffective.

Both current tree fixtures also time out with a 60-second verification budget
and 95-second outer watchdog (60.42 and 60.70 seconds session wall). This shows
persistence through the tested budget, not nontermination or impossibility.

## Evidence and next work

The [machine report](timeout-followup.json) preserves all 49 untraced runs and
four diagnostic captures, including commands, settings, errors, artifact hashes,
original outcomes and trace comparisons. The
[compressed evidence](evidence/timeout-triage/README.md) contains actual results,
raw output, solver streams, fixture bytes and runner/collector scripts.
All 53 sessions have completed supervisors, empty pending-process lists and no
protocol parsing errors. Backend cleanup warnings from timeouts remain recorded;
supervisor cleanup does not establish warning-free backend teardown.

The append trace has no audit gaps. The three timeout traces each lack only the
final check response, as expected after cancellation, and have incomplete solver
metadata because the relay was killed. Postflight checks confirm all 21 historical
artifact/fixture entries and all 851 archived source files are unchanged. Current
binary and Z3 hashes also match each experiment's plan. The active Prusti worktree
was not modified.

Next, stabilize allocation assumptions, address append's trigger completeness,
and repeat the focused comparisons. Increasing every timeout is not a substitute
for those fixes. No finite timeout screen can establish that every remaining
quantified proof eventually completes; some may need better triggers,
intermediate lemmas or encoding changes.
