# Separate instrumentation experiment preparation

This is a staged, fake-checked runner, not a completed experiment. It binds the validated four-fixture oracle, primary settings/evidence, pinned runtime source, full recorded VPR inventories, plain and timed binaries/classes, real v2 accounting gate and tools. `spec.json` records the hashes and expected commands. Re-run preflight if any input changes; the runner checks the bound bytes before and after each trial and at postflight.

The seed-43 schedule has 48 randomized blocks, each with a randomized order of plain, timed and timed-plus-accounting variants: 144 serial three-request sessions for four cases, native/source, configurations 1 worker/branch off and 4 workers/branch on, and three repetitions. A block is eligible for a within-block overhead comparison only when all three variants are valid and exact raw compatibility records agree; censored or invalid trials remain visible. Per-request timed phase records, raw output, timers, CPU accounting and hashes are retained. Source and native phase names and span boundaries differ; nested spans cannot be summed. Solver CPU and the frontend/runtime/wrapper/other residual are process CPU estimates, not elapsed-wall components. Missing attribution is invalid, not zero; GNU time CPU precision is typically 0.01 seconds.

After both primary measurements and an explicit solver-slot grant, invoke:

```sh
python3 tools/performance/profile/run.py --spec /tmp/ferrum-stage5-profiling-preparation/spec.json --output NEW_OUTPUT_DIRECTORY
```

This experiment is separate from the uninstrumented primary timings. The fake tests validate schedule and basic classification, not real verifier behavior or runtime overhead. Existing real accounting controls cover only the bounded fixtures and configurations recorded in their report.
