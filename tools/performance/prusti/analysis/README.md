# Direct Prusti analysis

`analyze.py` independently audited the completed primary run: all 576 requests
and 144 service cleanup audits passed. The [direct Prusti report](../../../../porting/performance-prusti.md)
records results and limits. To audit another completed run, create a new output
directory with:

```sh
python3 tools/performance/prusti/analysis/analyze.py \
  --run /ABSOLUTE/COMPLETE-PRIMARY-RUN \
  --output /ABSOLUTE/NEW-ANALYSIS-DIRECTORY
```

It requires the primary protocol's four cases, three pairs, seed 42, one/two/four workers, branch off/on, fresh and service modes, three serial requests per service, and 180-second verifier/300-second client limits. It checks sequential block IDs and valid backend order, the 144 randomized paired schedule blocks, 576 requests and 144 backend service cleanup audits, schedule and frozen artifact hashes, the four seed trees, postflight status, per-request expected outcome and Rust error/location, exact phase records, dependency build events, GNU timer format and raw file, raw client/session output, service segment hashes and complete service cleanup. The runner's raw rows must match `effective-trials.jsonl` after service-block-wide cleanup invalidation. Audit failures prevent performance aggregates. Sample-level failures and censored observations remain in the per-request audit and exclude the relevant samples; zero denominators are not converted to ratios.

For each case, backend and setting it groups fresh request, service-first request, and the mean of later requests 1 and 2 **within each service block**, so the three blocks, not six later requests, are the independent replicas. Service launch-to-socket startup is recorded once per block and grouped separately. JVM/native ratios require both valid observations in the same scheduled pair and positive native wall time. Within-backend worker ratios (at fixed branch setting) and branch-on/off ratios (at fixed worker count) match by pair index across separate randomized blocks, not the same service process; they are scoped exploratory comparisons. It retains individual values, median and range, audit reasons, and excluded pair indices. CPU in a service client excludes the still-running server and Z3; phase boundaries are inclusive and differ across backends. GNU time has limited precision; three pairs are not universal proof of performance.

`service-lifecycle.md` records the pilot's process-level JVM `OnceLock` reuse and per-request verifier/frontend construction. No standalone Silicon ff386 and bundled Prusti JVM results are pooled. This analyzer does not run verifiers, change raw observations or silently replace failed attempts.
