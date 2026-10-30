# Comparable saturation settings on Prusti-generated workloads

The full older weights are a promising candidate on the nested native case,
but this experiment does not establish a broadly faster default. Its median
paired native capture-wall ratio was **0.910** versus the newer weights: about
9% lower, with individual ratios ranging from 0.713 to 1.076. Quantifier work
was lower in all three matched observations, but fresh native captures also
varied in declaration order and solver work under identical settings.

Enabling only before-repetition saturation behaved very differently: its
native nested-case median paired wall ratio was **2.188**, with a wide range
of 0.775–2.812. The interactions between saturation sites matter. This does not
justify restoring one weight or changing a global default from a single case.

All **58 captures passed independent audit**: 48 positive trials verified and
ten negative controls retained the expected error ID and source span. No
observations were invalid or censored. Artifact hashes, cleanup, effective SMT
options/budgets, complete streams and fixed-path replay responses all passed.

## What was compared

Both native Ferrum `afdf10c` and bundled Silicon `6b540aa4` received these explicit
vectors with the same 100 ms saturation base. Order is preamble, contract,
unfold, inhale, repetition.

| Profile | Weights |
| --- | --- |
| Modern | `[1,0.5,0.4,0,0]` |
| Repeat only | `[1,0.5,0.4,0,0.02]` |
| Full older | `[1,0.5,0.4,0.2,0.02]` |
| Common off | `[1,0,0.4,0,0]` |
| Common on | `[1,0,0.4,0,0.02]` |

The slow `mut_element_nested_pass` input received all five profiles; the smaller
`mut_element_array_pass` received the first three. Each profile/backend/case
cell has three fresh captures. `mut_element_array_wrong` ran once under every
profile/backend as a readiness control and is excluded from latency aggregates.
Within each case/repetition block, profile/backend order was randomized before
execution, as was main-block order. The complete seed-20261030 schedule was frozen.

Equal vectors do not fully align older/newer call-site policy. The older bundle
uses the contract slot at several places where Ferrum uses inhale. The common
pair suppresses both slots, including genuine precondition saturation, and
isolates repetition under that altered policy. It is neither version's default.
Actual call categories and resource budgets were audited, rather than inferring
effective behavior solely from the supplied vector.

The [frozen protocol](performance-saturation-protocol.md) records exact settings
and hashes. These are parsed-Viper diagnostic runs with recording enabled, on
development builds. All trial and offline-solver descendants used logical CPUs
0–3, the host's two physical performance cores. They ran serially with ordinary
background activity and powersave governors; there was no exclusive core
reservation or fixed frequency. These timings are separate from earlier runs
with different affinity, load and instrumentation.

## Captured elapsed time

Seconds are median [minimum, maximum] across three observations. Capture wall
includes frontend work, startup, relay and shutdown. It is not direct Rust
encoding time or exclusive solver CPU.

| Case | Backend | Modern | Repeat only | Full older |
| --- | --- | ---: | ---: | ---: |
| Nested | Ferrum | 32.433 [27.314, 35.356] | 59.753 [27.413, 91.215] | 25.225 [24.865, 34.902] |
| Nested | Silicon | 18.402 [18.085, 26.260] | 23.726 [18.150, 28.671] | 25.947 [17.454, 28.642] |
| Array | Ferrum | 2.334 [2.127, 3.217] | 2.123 [2.026, 4.302] | 2.180 [2.125, 2.222] |
| Array | Silicon | 7.945 [7.625, 15.381] | 8.209 [7.743, 14.909] | 8.321 [7.529, 11.208] |

Matched ratios below divide profile time by modern time within the same
predeclared repetition index, then take the median and range. They are not
ratios of the displayed group medians. Below one means the numerator was lower.

| Case | Backend | Repeat-only / modern | Full-older / modern |
| --- | --- | ---: | ---: |
| Nested | Ferrum | 2.188 [0.775, 2.812] | 0.910 [0.713, 1.076] |
| Nested | Silicon | 1.092 [0.986, 1.312] | 0.988 [0.965, 1.556] |
| Array | Ferrum | 0.953 [0.910, 1.337] | 0.952 [0.661, 1.025] |
| Array | Silicon | 0.974 [0.969, 1.077] | 0.948 [0.729, 1.091] |

Every comparison has three complete pairs. The older profile is not faster
in every pair, and overlap and variability limit generalization. In particular,
the lower native nested ratio of group medians must not be substituted for the
more modest 0.910 median matched ratio.

## Solver work and the policy interaction

Each captured stream was replayed through a fresh identical Z3 with its resource
limits intact, followed by a statistics query. Every original response prefix
matched exactly. CPU and statistics sum the source's separate owner/worker
processes only within their own trial. Fixed-path replay does not rerun verifier
decisions. Absent statistics remain unavailable; they are never zero-filled.

The following are median [range] of the three matched profile/modern ratios:

| Case | Backend | Profile | Quantifier instantiations | Resource counter |
| --- | --- | --- | ---: | ---: |
| Nested | Ferrum | Repeat only | 2.480 [0.278, 7.048] | 2.068 [0.488, 3.367] |
| Nested | Ferrum | Full older | 0.435 [0.217, 0.960] | 0.586 [0.455, 0.956] |
| Nested | Silicon | Repeat only / full older | 1.557 [1.557, 1.557] | 1.133 [1.133, 1.133] |
| Array | Ferrum | Repeat only | 1.043 [1.043, 1.090] | 1.033 [1.032, 1.035] |
| Array | Ferrum | Full older | 1.181 [1.129, 1.228] | 1.152 [1.148, 1.155] |
| Array | Silicon | Repeat only / full older | 1.082 [1.082, 1.082] | 1.025 [1.025, 1.025] |

On the native nested case, the older profile's median matched quantifier count
was about 56.5% lower, while the array case's was about 18.1% higher. Native
repeat-only nested captures ranged from 67,518 to 1,062,396 instantiations and
5.557 to 71.346 seconds of offline solver CPU. Thus a repeat-only restoration
is particularly sensitive on this case and cannot stand in for the full policy.

The common-policy comparison gives a different result. These ratios compare
common-on with common-off on the nested case, with both moved slots disabled:

| Backend | Capture wall | Offline solver CPU | Quantifier count | Resource counter |
| --- | ---: | ---: | ---: | ---: |
| Ferrum | 0.689 [0.594, 0.727] | 0.692 [0.549, 0.749] | 0.661 [0.648, 0.716] | 0.788 [0.771, 0.879] |
| Silicon | 0.712 [0.615, 1.054] | 0.660 [0.530, 0.661] | 0.586 [0.586, 0.586] | 0.680 [0.680, 0.680] |

Repetition was beneficial in this altered-policy sample on both backends by the
median metrics, whereas it increased work with normal contract saturation in
the bundled source and varied widely in native. That supports testing complete
policy combinations; it does not select the common control as a new default.

Call-site differences remain visible. On nested full-older captures, native
logs 33 after-contract, 69 after-inhale, and 34 before-iteration saturations;
source logs 102 after-contract and 34 before-repetition saturations. Those
contract/inhale categories have different weight-derived budgets even under
the same vector. Common controls suppress both categories on both backends.
Raw renderer/category distinctions and actual per-query budgets remain in JSON.

## Fresh native captures are not deterministic

Every native positive profile has three distinct raw and canonical command
stream signatures; each source positive profile has one signature repeated
across its three captures. The canonical signature removes token spacing only.
It is not semantic normalization.

This is more than a generated-name difference: the first differing canonical
command among native nested modern captures is command 34, a sort declaration:
`s_0_Tuple`, `s_visit$col$$col$$lc$closure$oc$0$rc$`, or
`ParamTyp_make_generic_s_Ref_mutable`, depending on the run. Identical settings
therefore change real command order. Its causal contribution to the variance
is not isolated, but it confounds attribution of every observed counter change
to the weights. Exact response replay of a fixed stream does not prove stable
emission or counters across fresh verifier captures.

The next step should stabilize native sort/preamble emission, then repeat this
same comparison and extend it to direct Prusti and more stdlib cases before
promoting a global default. The full older profile is a useful tuning candidate
for the nested case; the evidence does not support a blanket restoration.

## Evidence and checks

The [machine report](performance-saturation.json) includes all 58 trial records,
the independent audit, per-repetition ratios and ranges, stream signatures,
commands, settings, raw saturation categories and artifact hashes. The
[retained evidence](evidence/saturation/README.md) includes complete nested
wire/prover captures for repetition zero of every profile/backend, selected by
index rather than result. All other raw files remain hash-linked locally under
`/tmp/ferrum-saturation-results-v2`.

The first six-control V1 attempt is retained separately: every expected proof
outcome was met, but the recorder lost a final forwarded command and the gate
stopped before any positive trial. A versioned persist-before-forward recorder
passed real byte-equality/protocol checks and 20 immediate-kill-after-ack tests;
the complete unchanged schedule restarted as V2. Independent audit initially
rejected equivalent CPU-mask spellings, then passed after correcting the auditor;
the measured data were unchanged and both audit attempts are retained.

Source aggregate decision statistics are unavailable when its owner omits the
field. This conservative handling also corrects the earlier fixed-trace
report's combined-decision percentage; its quantifier/resource totals remain
supported. No runtime implementation or global defaults were changed here.
