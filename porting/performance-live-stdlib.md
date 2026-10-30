# Live profiling of the stdlib adoption run

On 2026-10-30, two short CPU profiles were collected from the already-running
Ferrum iterator suite after the user reported slow progress. The sampled windows
show substantial Z3 work, particularly quantifier matching. This is a different
workload and measurement scope from the earlier four-case performance study.

The verification runs continued. Their binaries, flags, logs and results were
not changed. Sampling and subsequent symbolization can perturb overlapping
timings; the [machine record](performance-live-stdlib.json) identifies the
examination interval. Treat those timings as observational rather than adding
them to the earlier uninstrumented comparisons.

## Completed-case comparison before profiling

At initial inspection, Ferrum had completed 232 of 320 iterator clients;
Silicon had completed all 320. The 232 common clients had matching Rust source
hashes. Of these, 205 met their expected result and diagnostic on both backends;
their median individual Silicon/Ferrum elapsed-time ratio was 2.55. The other
27 pairs remain in the machine record and are excluded from that ratio.

The typical completed case favored Ferrum, while several harder cases favored
Silicon substantially:

| Case | Ferrum seconds | Silicon seconds | Ferrum/Silicon |
| --- | ---: | ---: | ---: |
| `mut_native_mut_ref_write_false` | 155.23 | 42.89 | 3.62× |
| `mut_native_mut_ref_restoration_wrong` | 177.27 | 67.69 | 2.62× |
| `mut_native_mut_ref_restoration_false` | 160.73 | 63.27 | 2.54× |
| `mut_element_nested_pass` | 80.17 | 34.93 | 2.30× |

These are single regression-run observations. Runs overlap, their adapters were
built from different commits, and the completed subset omits pending cases and
excludes mismatches/timeouts from ratios. They are not a controlled speedup
estimate. Matching Rust source also does not establish identical verification
obligations. For `mut_element_nested_pass`, however, the retained Viper dumps
are byte-identical: 461,392 bytes, SHA-256
`9fbeab0cc9dc824772c9c5bfa06765a62998ca1141a56151b15f25068e38b3e7`.

The Ferrum build uses adapter `474b7ae1d` and runtime `afdf10c`; the Silicon
build uses Prusti `c108c1c36` and the bundled Silicon `6b540aa4`. The intervening
code change preserves opaque-function/reveal annotations in the native adapter.
Both runs use one verifier worker and branch parallelism off, with 180-second
program and 300-second outer command limits for this suite. No explicit solver
time-bound override was supplied. Build manifests and per-case records are retained
separately from the checkout revision reported when a later suite starts.

## Attached CPU samples

`perf record` attached to each existing driver and its existing Z3 child using
`cpu-clock:u`, 49 Hz and 8 KiB DWARF stack capture. Requested windows were bounded
at 20 seconds; the usable sample spans were shorter. No debugger stopped the
verifiers, no new solver was launched and no kernel settings were changed.

| Case | Perf sample span | Samples | Z3 samples | Z3 stacks through quantifier matching |
| --- | ---: | ---: | ---: | ---: |
| `mut_native_restoration_wrong` | 4.284 s | 191 | 121 (63.4%) | 69/121 (57.0%) |
| `mut_native_shared_ref_two_yields_wrong` | 9.506 s | 441 | 322 (73.0%) | 204/322 (63.4%) |

The first recorder exited with signal 15; its readable partial capture is
retained. A second attempt against `mut_native_shared_ref_two_yields_false`
failed because the process disappeared during attachment and yielded no usable
profile. The third attempt exited successfully. Both readable captures report
zero lost samples. The sampled negative cases subsequently met their expected
diagnostic in the ongoing harness.

The matching stacks pass through `smt::quantifier_manager::propagate`,
`mam_impl::match` and the matching interpreter's `execute_core`, `get_next_f_app`
and `get_first_f_app`. This identifies quantifier matching as a hotspot in the
observed Z3 windows. It does not identify the responsible quantified formula,
count individual solver queries or establish the cause of a whole-case slowdown.

Independent `/proc` counters sampled the same process identities, verified by
PID and start tick. Their common observation intervals differ from perf's spans:

| Case | Counter interval | Driver CPU | Z3 CPU | Z3 share of these CPU deltas |
| --- | ---: | ---: | ---: | ---: |
| Restoration | 4.107 s | 1.39 s | 2.71 s | 66.1% |
| Shared reference, two yields | 8.513 s | 1.96 s | 6.45 s | 76.7% |

CPU includes user plus system time for the observed processes. These shares
describe only the recorded intervals and are not fractions of entire verification
wall time. User-space sample proportions are a separate estimate and need not
equal these counter shares.

Native instruction-pointer samples also show allocation/freeing, hashing,
expression equality, term serialization and collection work. Native call-chain
recovery is limited: 46/70 and 76/119 non-Z3 samples have no recovered stack in
`perf script`. Flat instruction-pointer symbols remain available for these
records, but the missing callers prevent a reliable ownership/allocation-path
breakdown. The earlier 12–21% Z3 CPU shares measured parsed sessions for four
smaller workloads; they must not be generalized to these hard direct-Prusti cases.

## Next investigation

Replay a selected slow case separately after the current suite completes, with
the same preserved Viper input on both backends. Capture SMT command streams,
effective solver options, query boundaries and quantifier statistics. Compare
trigger/axiom emission, repeated assertions and solver-call ordering, then test
any suspected difference against the same expected result and diagnostic. The
live profiles supply this lead; they do not yet select a sound algorithm change.

A separate native profile with better stack recovery can investigate hashing,
equality, allocation and SMT serialization. More verifier workers may overlap
independent work, but enabling them does not itself divide an already-issued
solver query across workers. This observation does not settle whether branch
parallelism helps these whole cases.

The [machine record](performance-live-stdlib.json) preserves the 232 completed
case pairs, exclusions, profile metadata, CPU snapshots/deltas, sample aggregates,
flat symbols and raw artifact hashes. Raw captures and decoded stacks remain
under `/tmp/ferrum-live-profile-20261030T150437Z`; they are not embedded binaries
in the repository. The original ongoing suite evidence remains under
`target/stdlib-im5-dual229/ferrum` and `target/stdlib-im5-dual226/silicon` in the
stdlib checkout.
