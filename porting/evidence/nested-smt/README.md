# Nested SMT evidence

`manifest.json` records commands, input/tool/solver/jar hashes, successful runs
and the separately retained rejected source-flag attempt. `controls.json` records
real direct/relayed protocol controls. The native, source-owner and source-worker
directories contain gzip-compressed original SMT stdin/stdout/stderr and chunk
timestamps, metadata, both offline replay outputs and final statistics. The
machine report at `../../performance-nested-smt.json` binds the recorded data files by hash.

Gzip timestamps are fixed at zero. Uncompressed byte hashes and lengths remain
in the machine report. The original generated Viper input is preserved in
`../../../tools/performance/fixtures/mut_element_nested_pass.vpr`.

To audit a transcript, decode it into a new directory using these names:

| Compressed file | Decoded file |
| --- | --- |
| `stdin.smt2.gz` | `stdin.bin` |
| `stdout.txt.gz` | `stdout.bin` |
| `stderr.txt.gz` | `stderr.bin` |
| `chunks.jsonl.gz` | `chunks.jsonl` |

Copy `metadata.json`, then run
`python3 tools/performance/smt/analyze_trace.py DECODED_DIRECTORY --output NEW_REPORT.json`
from the repository root. Original relay metadata may lack an exit field because
the verifier terminates its solver process. Stream completeness/alignment and
supervisor cleanup are independently checked in the report.

For solver-only reproduction, append `(get-info :all-statistics)` to decoded
stdin and send it to the manifest's Z3 executable with `-smt2 -in`. Compare the
entire original response prefix before interpreting the final statistics.
The `offline-replay` and `offline-replay-reverse` captures retain both runs. Exact
work counters repeated here; timing was variable on the shared host. This follows
a fixed captured path rather than rerunning verifier decisions.
