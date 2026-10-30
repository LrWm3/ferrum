# Backend result audit and analysis

The completed primary run passed all 480 trials and 240 paired-block audits;
see the [backend report](../../../porting/performance-backend.md). To audit a
completed run, choose a new output path and invoke:

```sh
python3 tools/performance/analysis/analyze.py /tmp/ferrum-stage5-backend-results --output /tmp/ferrum-stage5-analysis/backend-report.json
```

The tool refuses to overwrite the output. It independently checks the four-case, five-repetition, 240-block/480-trial schedule; unique ordered trial IDs and source/native order; cache policy, command, artifact hashes, postflight summary, session/timer hashes, timer data and expected proof outcome plus error ID/position multiset. Missing, duplicate, malformed, censored or invalid records never become zero-valued timings. Integrity problems are recorded and give a nonzero exit; inspect them before considering any result.

Per case/configuration/mode/backend, the report retains classification counts and valid verifier-command elapsed wall median/min/max. Each source/native ratio is calculated only from a complete valid within-block pair; missing, invalid, censored and zero-rounded pairs are counted as excluded. `source_over_native` has median/min/max plus every retained pair. Worker/branch values are ratios of each group's median to the same case/backend/mode's one-worker, branch-off median; they are not matched-repetition effects. No aggregate across workloads is produced.

GNU time provides coarse decimal wall seconds, often hundredths; zero values are included as coarse observations in group statistics but excluded from ratios. Reused mode is one **three-request aggregate session**, never divided into per-request values or treated as three samples. The data are inclusive verifier-command wall, not symbolic execution or Z3-only time. Hash checks and prior trials warm caches; randomized order reduces but cannot eliminate drift and environmental differences.

Synthetic-only validation (no solver or verifier) checks that one missing trial and one invalid paired trial do not become valid or enter paired ratios:

```sh
python3 tools/performance/analysis/test_analyze.py
```
