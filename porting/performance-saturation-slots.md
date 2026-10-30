# Isolating inhale and repetition saturation

Both saturation slots make the separate method solver do more work on the nested
case. **Before-repetition is the larger individual regression**, but neither slot
alone reproduces the earlier severe timeout. The severe observed slowdown is an
interaction when both are enabled. Current separate-solver settings, with both
extra slots disabled, remain the best of the three settings tested here.

No runtime code or defaults changed. All binaries still match the previous
`dd263e8` runtime. The complete screen took **470.4 seconds (7.8 minutes)**.

## Fixed settings and checks

Every run used `--separateMethodSolver=true`, one worker, branches off, internal
caches on, the same generated inputs and Z3 binary, affinity `0,1,2,3`, and the
existing development build profile. The saturation base remained 100 ms:

| Profile | Weights: preamble, contract, unfold, inhale, repetition |
| --- | --- |
| Current | `[1,0.5,0.4,0,0]` |
| Inhale only | `[1,0.5,0.4,0.2,0]` |
| Repetition only | `[1,0.5,0.4,0,0.02]` |

Passing and failing array controls ran once per profile. Nested captures then
used current, inhale, repetition, repetition, inhale, current order. Untraced
phase sessions used the same mirrored order for each positive input. Limits
remained 60 seconds for verification, 90 for the outer supervisor and 45 for each
offline replay. A declared rule would have retained a new-profile nested timeout
and skipped that profile's later runs while continuing the independent settings.
No profile needed to be excluded, and no run was retried or had its budget raised.

All **12 captures, 24 solver-stream replays and 12 untraced sessions** passed.
Nested SMT input/output streams and work counters matched exactly between each
profile's two captures. Current-mode streams also matched the earlier references.
The wrong-array controls retained `exhale.failed:assertion.false` at
`mut_element_array_wrong.vpr@1786.10--1786.82`. Supervisors reported complete
cleanup, and every frozen artifact retained its hash.

The both-enabled configuration was **not rerun**. Its timeout and prefix diagnosis
remain historical observations from the
[preceding interaction test](performance-method-saturation.md).

## Reproducible nested solver work

All totals include the owner and the single method-worker solver.

| Profile | Checks | Instantiations | Z3 resource count | Resource change from current |
| --- | ---: | ---: | ---: | ---: |
| Current | 1,112 | 137,899 | 14,890,364 | — |
| Inhale only | 1,181 | 187,870 | 19,581,006 | +31.5% |
| Repetition only | 1,146 | 339,617 | 25,107,897 | +68.6% |

Inhale-only adds 69 saturation checks and **36.2% more instantiations**.
Repetition-only adds 34 checks and **146.3% more instantiations**. Each complete
counter result reproduced exactly. Separate fixed-stream replay CPU was:

| Profile | Two replay CPU observations, summed over owner and worker |
| --- | --- |
| Current | 6.85 s, 6.85 s |
| Inhale only | 7.45 s, 7.16 s |
| Repetition only | 12.84 s, 15.19 s |

These CPU measurements are separate replays, not exclusive portions of the live
backend intervals.

## Matching the earlier slow checks

All five previously identified slow assertions match byte-for-byte in the
current, inhale-only, repetition-only and historical both-enabled worker traces.
Their effective options also match, including `rlimit=5000000`. Their summed live
response waits in the first capture were:

| Profile | Sum for the five matched checks |
| --- | ---: |
| Current | 0.234 s |
| Inhale only | 0.246 s |
| Repetition only | 0.537 s |
| Both, historical timeout run | 37.360 s |

There is stronger evidence than matching only those final assertions. After
omitting **only `check-sat` and `set-option :rlimit`**, all **10,278 remaining
commands** in each complete worker stream have the same ordered canonical hash:

```text
02fe6f1728783f1970965ba321944564992020c8b7bf80b8a724c22fc26f0e1f
```

This comparison preserves declarations, definitions, assertions, push/pop,
other options and all other commands. The historical both-enabled stream is
truncated, so its whole stream cannot match. Its corresponding filtered prefixes
through each of the five matched checks do match the other profiles exactly.

Thus the observed search regression occurs with the same encoded formulas and
scopes, after changing solver probes and resource-limit updates. This supports a
search-history interaction between the two saturation settings. It does not
equate Z3's internal learned state across those different histories or establish
that these options behave the same way on other inputs.

## Timing observations

The untraced timing stage used the real solver directly, without the trace relay
or prover log. Backend time is `session_verify_inclusive`; it includes solver
time and excludes frontend parsing and analysis. Values below are paired by
the first and second passes through the mirrored schedule.

| Nested profile | Backend seconds | Backend/current ratios | Whole-session seconds |
| --- | --- | --- | --- |
| Current | 11.616, 8.850 | — | 30.799, 24.910 |
| Inhale only | 10.121, 9.054 | 0.871, 1.023 | 31.530, 27.470 |
| Repetition only | 14.506, 20.145 | 1.249, 2.276 | 30.515, 38.972 |

Inhale-only backend timings moved in opposite directions; whole-session timing
was higher in both pairs. Repetition-only backend timing was higher in both
pairs, but its first whole-session observation was slightly lower because other
phases varied. For example, unchanged semantic analysis ranged from 12.26 to
16.76 seconds across the nested sessions. Two pairs on a shared host therefore
do not establish precise causal latency percentages; the reproducible counters
and exact-stream replays provide the stronger evidence of increased work.

The small passing array also paid more work:

| Array profile | Checks | Instantiations | Resources | Backend/current ratios |
| --- | ---: | ---: | ---: | --- |
| Current | 407 | 1,280 | 819,033 | — |
| Inhale only | 476 | 1,456 | 891,944 | 1.120, 1.276 |
| Repetition only | 416 | 1,338 | 838,787 | 1.363, 1.072 |

For the separate solver on these inputs, leave both extra saturation slots
disabled. The earlier retained-solver/older-weights result still has the lowest
completed nested solver-work count, but that is a different lifecycle and remains
workload-specific. This screen identifies no new setting to promote and adds no
new direct-Prusti timing, full Rust verification matrix or pinned-Silicon run.

The [machine report](performance-saturation-slots.json) preserves the frozen
schedule and hashes, every capture and timing observation, exact replay checks,
paired ratios, complete command-comparison results and runner sources. Raw
evidence is under `/tmp/ferrum-saturation-slots-dd263e8`.
