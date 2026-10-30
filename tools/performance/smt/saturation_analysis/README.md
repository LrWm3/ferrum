# Independent saturation audit

This read-only analyzer audited all 58 V2 captures successfully. It independently
checks the fixed schedule, outcomes and error spans, supervisor cleanup, artifact
inventories, wire/chunk protocol, effective options and resource budgets, replay
response prefixes/statistics and matched aggregates. Missing statistics remain
unavailable and invalid observations remain visible.

To audit the complete retained local run into a new output directory:

```sh
python3 tools/performance/smt/saturation_analysis/analyze.py \
  --results /tmp/ferrum-saturation-results-v2 \
  --spec porting/evidence/saturation/spec.json \
  --preview porting/evidence/saturation/schedule-preview.json \
  --trace-tool tools/performance/smt/analyze_trace.py \
  --output /tmp/ferrum-saturation-new-audit
```

The spec still refers to the original frozen local binaries, classes and inputs.
Their existence and matching hashes are required. The selected compressed
evidence in the repository is not a complete archive of that 1.2 GB run or its
executables. See the [results](../../../../porting/performance-saturation.md).

Run `python3 tools/performance/smt/saturation_analysis/test_analyze.py` for
synthetic rejection checks covering wrong error positions, invalid/missing metric
exclusion and missing effective options/resource budgets. The real experiment
audit supplies separate evidence of actual capture/replay behavior.

Each eligible repetition retains raw and ordered canonical-command signatures.
Canonicalization removes token spacing only, without alpha-renaming or semantic
normalization. Fixed-path replay consistency and variation between independently
generated streams are different properties. Source counters/CPU sum its separate
solver processes only when all required statistics are present; relay waits are
not exclusive CPU. Equal weight vectors do not align older/newer call sites.

The initial audit rejected equivalent CPU-mask spellings. The corrected version
accepts the frozen mask and retains the original audit as prior evidence; no
measurements were changed to pass the audit.
