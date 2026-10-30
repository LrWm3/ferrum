# Separate instrumentation experiment

The completed experiment passed all 144 sessions and 48 matched-block audits;
see the [profiling report](../../../porting/performance-profile.md). The runner
binds the validated four-fixture oracle, primary settings/evidence, pinned runtime
source, full recorded VPR inventories, plain and timed binaries/classes, real v2
accounting gate and tools. `spec.json` records the hashes and expected commands.
Create a new spec and re-run preflight if any input changes; the runner checks
the bound bytes before and after each trial and at postflight.

The seed-43 schedule has 48 randomized blocks, each with a randomized order of plain, timed and timed-plus-accounting variants: 144 serial three-request sessions for four cases, native/source, configurations 1 worker/branch off and 4 workers/branch on, and three repetitions. A block is eligible for a within-block overhead comparison only when all three variants are valid and exact raw compatibility records agree; censored or invalid trials remain visible. Per-request timed phase records, raw output, timers, CPU accounting and hashes are retained. Source and native phase names and span boundaries differ; nested spans cannot be summed. Solver CPU and the frontend/runtime/wrapper/other residual are process CPU estimates, not elapsed-wall components. Missing attribution is invalid, not zero; GNU time CPU precision is typically 0.01 seconds.

Run separately from the primary measurements, with exclusive use of the benchmark
solver slot and a new output directory:

```sh
python3 tools/performance/profile/run.py --spec /tmp/ferrum-stage5-profiling-preparation/spec.json --output NEW_OUTPUT_DIRECTORY
```

This experiment is separate from the primary timings. The fake tests validate
schedule and basic classification; the completed run supplies the real behavior
and overhead observations. Overhead varied substantially and does not support a
stable correction factor. Real accounting controls cover only the bounded
fixtures and configurations recorded in their report.
