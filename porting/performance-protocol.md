# Performance protocol

The corrected compatibility comparison is complete; see
[the final comparison](compatibility-final.md). This protocol is specified before
primary timed trials. The runtime remains `afdf10c`; measurement tools do not
alter its production implementation or optimization settings.

## Questions and scope

Measure fresh-process cost, session reuse, worker-count/branch effects and the
available encoding/backend/solver components on actual stdlib workloads. This
is a comparison of Ferrum and the specified Silicon builds, not a Verus study.
Four cases are selected before timing: sequence `observation_pass`, iterator
`mut_element_array_pass`, `mut_element_option_pass`, and the expected failure
`mut_element_array_wrong`. Each fresh native/JVM Rust calibration must produce
the expected result and byte-identical Viper dumps. Preserve exact Rust and Viper
source hashes and the negative diagnostic oracle.

Standalone parsed-Viper uses Silicon `ff386aec` with Silver `c4f54b84`; direct
Prusti uses integration build pin `a59ed917c` and its separately hashed bundled
JVM backend. Do not pool these as the same source backend. All primary runs use
stdio Z3 4.16, internal Silicon caches enabled, and Prusti result caching disabled.
Frozen dev artifacts retain their existing package optimization settings; this
is not a release-build comparison.

## Primary schedules

Run serially on the same host, without concurrent agent builds or solver runs.
Use 1, 2 and 4 verifier workers with branch parallelism off and on. Randomize
complete blocks and backend order using seed 42; retain the schedule in advance.

- Parsed Viper: five paired repetitions per case/configuration/mode, fresh one
  request and reused three-request sessions. This gives 480 verifier processes.
  Verifier timeout 120 s; outer bound 150 s per request plus 30 s cleanup grace.
- Direct Prusti: three paired repetitions per case/configuration/mode, fresh
  process and a new service with three serial client requests. This gives 576
  client requests and 144 service starts. Verifier timeout 180 s; outer client
  bound 300 s. Keep socket-ready startup, first request and later requests separate.

Bounded harness pilots are excluded from primary results. Check exact proof/error
outcomes and complete protocol/cleanup after every trial. Source/artifact changes
stop the run. Censored timeouts, failures and invalid cleanup remain reported;
never replace them with favorable retries. Invalidate every request belonging to
a failed service-cleanup block, even if failure is recorded after those requests.

## Measurement and analysis

Primary wall comes from GNU time around the command, with 0.01 s typical
resolution. Record raw wall, CPU, maximum RSS, commands, phases, host load,
toolchain, flags and artifact inventories. Setup, seeded dependency copies and
fixture cleaning are outside timing; require no dependency rebuild in the timed
Rust requests. Hash checks warm OS caches. Fresh process is not cold disk cache.

Report medians and ranges by workload/configuration/mode, all trial counts and
exclusions, paired source/native ratios, and within-backend worker/branch effects.
Use complete valid pairs; do not average unlike workloads or treat repeated
requests in one service as independent replicas. A small repeated experiment
supports scoped observations, not a universal verifier speed claim.

Keep instrumentation studies separate. Existing direct Prusti encoding,
conversion and backend spans are inclusive and have different backend boundaries.
Tools-only phase spans need behavior and overhead controls. Z3 CPU accounting
must survive forced solver shutdown and reconcile every process identity; absent
records are unavailable, not zero. Z3 process CPU includes startup, parsing,
solving and cleanup. Wall phases overlap, so no subtraction yields exclusive
symbolic execution. Report an unresolved component explicitly if reliable
measurement is unavailable.

For the separate parsed-Viper instrumentation study, use all four selected cases,
the 1-worker/branch-off and 4-worker/branch-on configurations, and three-request
reused sessions. Schedule three repetitions of plain, phase-instrumented, and
phase-instrumented plus solver-accounting variants for each backend: 144 process
sessions in total. Freeze randomized blocks and variant order with seed 43 before
execution. Compare phase instrumentation against plain and accounting against
phase-only within complete valid blocks. Keep first and subsequent phase records
distinct. If accounting cannot pass real behavior and cleanup controls, retain
that failure and omit its CPU attribution rather than assigning missing cost zero.
