# Saturation experiment evidence

The [machine report](../../performance-saturation.json) preserves all 58 compact
trial records and the independent audit, including exclusions, matched ratios,
stream signatures and artifact hashes. This directory contains the frozen spec,
schedule/preview, summary and compressed raw trial stream.

`nested-rep0/` retains the complete original wire captures, annotated prover
logs, session output and offline responses/statistics for repetition index zero
of every nested profile/backend. This representative selection uses the fixed
index, not the measured result. Gzip timestamps are zero. Compressed and
uncompressed hashes/lengths are bound in the machine report.

For a selected solver, decode `stdin.smt2.gz`, `stdout.txt.gz`, `stderr.txt.gz`
and `chunks.jsonl.gz` into `stdin.bin`, `stdout.bin`, `stderr.bin` and
`chunks.jsonl` in a new directory, copy its `metadata.json`, then run
`tools/performance/smt/analyze_trace.py` as described in the tool README.
The V2 metadata labels `forwarded_ns` as forwarding start; waits use received
boundaries. Final exit metadata can be absent because the verifier terminates
the relay. Byte completeness/alignment and process cleanup are separate checks.

Replay the decoded stdin with the manifest's real Z3 and an appended
`(get-info :all-statistics)`. Compare the full original response prefix before
interpreting the final statistics. This follows a fixed captured path, not new
verifier decisions. All other repetitions, array captures and binaries remain
hash-linked under the full local run at `/tmp/ferrum-saturation-results-v2`.

`prior-readiness-v1-*` preserves the stopped six-control attempt. Every expected
proof outcome was met, but one final input command was absent from the recorder,
so the readiness gate prevented any main positive trial. V2 restarted the full
unchanged plan after the recorder fix; V1 is excluded from the new aggregates.

`initial-audit-cpu-mask.json.gz` preserves the auditor's initial false rejection
of equivalent affinity spellings. The corrected audit passed on unchanged data.
These instrumentation/audit corrections are distinct from proof failures or
performance observations.
