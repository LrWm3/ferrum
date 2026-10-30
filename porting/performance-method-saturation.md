# Solver lifecycle and saturation interaction

The follow-up [slot-isolation screen](performance-saturation-slots.md) is now
complete. Each slot alone verifies with more solver work, and the severe timeout
remains specific to their observed combined behavior. It also compares complete
filtered command streams and the corresponding prefixes of this timeout run.

The two individually promising settings **did not combine successfully on the
nested case**. Older saturation with a separate method solver hit the 60-second
verification limit. A bounded SMT-only diagnosis reproduced much more solver
work, so the result is more than a noisy whole-process timing observation.

No runtime code or default changed. The existing `dd263e8` binaries, including
cached term hashes and the opt-in method-solver flag, were reused unchanged.

## Four configurations and the early stop

Every configuration used one worker, branches off, internal caches on, the same
Z3 and generated input bytes, affinity `0,1,2,3`, and the existing development
build profile. The two varied settings were:

| Setting | Values |
| --- | --- |
| Method solver | Retained context / `--separateMethodSolver` |
| Saturation weights, base 100 ms | Current `[1,0.5,0.4,0,0]` / older `[1,0.5,0.4,0.2,0.02]` |

The weights are preamble, contract, unfold, inhale and repetition. The older
vector changes the last two slots together; this experiment does not isolate
their individual effects. Selecting the separate worker also changes its
preamble, symbols and history together.

The declared schedule was eight array controls, eight nested captures in mirrored
order, and sixteen untraced phase sessions. Each capture required the expected
proof/error outcome, complete protocol and replay checks before proceeding.
Program/outer/offline limits were 60/90/45 seconds, with no retries.

All eight controls passed. The first three nested configurations verified and
reproduced their earlier exact SMT streams and solver counters. The first
combined nested run timed out, so the declared gate stopped the experiment after
**214.1 seconds**. Four mirrored captures and all sixteen untraced timings were
therefore **not run**. This is a stopped experiment, not a completed two-repeat
timing matrix.

| Nested configuration | Capture elapsed | Quantifier instantiations | Z3 resource count | Outcome |
| --- | ---: | ---: | ---: | --- |
| Retained / current | 28.15 s | 181,264 | 18,540,052 | Verified |
| Retained / older | 24.95 s | 95,396 | 10,823,650 | Verified |
| Separate / current | 35.11 s | 137,899 | 14,890,364 | Verified |
| Separate / older | 76.92 s | Unavailable | Unavailable | Verification timeout at 60 s |

Successful totals include both owner and worker where applicable. The combined
worker stream is incomplete; its completed owner stream alone must not be
reported as a total. Capture elapsed time includes frontend, relay, logging and
shutdown costs on a shared host. It is not direct Prusti timing, and the timeout
is not a completed latency observation.

## Where the combination regressed

The separate/current and separate/older worker traces contain five **byte-identical
asserted formulas with identical effective solver options** in permission-removal
checks. Each had `rlimit=5000000`. They returned `unknown` in both configurations,
but their live response waits differed markedly:

| Current command / combined command | Current wait | Combined wait |
| --- | ---: | ---: |
| 12511 / 12749 | 0.037 s | 5.143 s |
| 12518 / 12756 | 0.138 s | 7.563 s |
| 12530 / 12768 | 0.048 s | 8.091 s |
| 12543 / 12781 | 0.045 s | 8.616 s |
| 12550 / 12788 | 0.041 s | 7.946 s |

These five completed checks accumulated **37.36 seconds**, versus **0.31 seconds**
with current saturation. All completed worker-query waits totaled 52.86 seconds
before the combined timeout. Cancellation occurred while command 12800, another
quantified permission-depletion check, awaited a response. Matching these local
formulas does not establish equivalence of their complete solver contexts or
histories.

The session reported `timeout.error`, with cancellation-time null-response and
broken-pipe cleanup warnings. The outer supervisor completed, reported no
protocol errors and reaped all owned processes (`cleanup_pending=[]`). Thus the
large completed-query waits precede the cancellation warnings; the warnings do
not explain the search slowdown.

## Bounded post-stop SMT diagnosis

One additional diagnostic compared fixed SMT prefixes through the first matched
slow check: current command 12511 and combined command 12749. It used fresh Z3
processes, the same original commands through that check, and a **30-second cap
per prefix**. Only `get-info :reason-unknown` and `get-info :all-statistics` were
appended. This was not a retry of full verification, and did not resume the
stopped benchmark schedule.

Both prefixes completed and exactly reproduced every original response through
the selected query:

| Prefix metric | Separate / current | Separate / older |
| --- | ---: | ---: |
| Z3 CPU | 5.98 s | 21.08 s |
| Quantifier instantiations | 128,695 | 539,090 |
| Z3 resource count | 13,591,859 | 47,934,659 |
| Final `unknown` reason | `(incomplete quantifiers)` | `canceled` |

The combined prefix required **3.52× the CPU, 4.19× the instantiations and 3.53×
the resource count**. The `canceled` reason came from a completed replay process
under the captured resource-bound settings, not from reaching the diagnostic's
30-second wall limit. These are prefix statistics, not totals for the unfinished
combined verification.

## Controls and implications

All four configurations verified the passing array and preserved the wrong
array's `exhale.failed:assertion.false` at
`mut_element_array_wrong.vpr@1786.10--1786.82`.

| Passing-array configuration | Checks | Instantiations | Resource count |
| --- | ---: | ---: | ---: |
| Retained / current | 406 | 1,337 | 613,017 |
| Retained / older | 484 | 1,602 | 706,520 |
| Separate / current | 407 | 1,280 | 819,033 |
| Separate / older | 485 | 1,579 | 913,999 |

Older weights added 69 after-inhale and 9 before-iteration saturations on this
array case. They added 69 and 34 respectively on the completed nested retained
run. The small case paid more solver work, reinforcing the workload dependence.

Retained/older remains the lowest solver-work result among the completed nested
configurations. The combined setting should not be promoted on this evidence.
The next narrow tuning question is whether after-inhale or before-repetition
saturation causes the separate solver's regression, using these matched checks
as diagnostics. Neither setting deserves a global default change from this run.

The [machine report](performance-method-saturation.json) preserves the original
schedule, all twelve observed captures including the timeout, seventeen exact
full-stream replays, missing totals/timings, matched-query evidence, the two
prefix diagnostics and artifact hashes. Every frozen artifact remained unchanged.
Raw evidence is under `/tmp/ferrum-method-saturation-dd263e8`. This experiment
adds no new full Rust matrix or pinned-Silicon comparison. The earlier
[lifecycle](performance-method-solver.md) and
[saturation](performance-saturation-short.md) observations remain separate.
