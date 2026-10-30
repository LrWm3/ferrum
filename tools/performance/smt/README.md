# SMT transcript capture and analysis

`trace_z3.py` is an executable relay selected as a verifier's Z3 executable.
Set `FERRUM_SMT_REAL_Z3` to the real solver and `FERRUM_SMT_TRACE_ROOT` to a new
capture directory. It forwards stdin/stdout/stderr bytes and records each stream
plus monotonic receive/forward timestamps and invocation metadata. Each solver
invocation has an independent directory, including version probes. It does not
inject options, queries or statistics requests. Verifier shutdown may kill the
relay before its final metadata update; keep that distinction from audited byte
completeness and outer-supervisor process cleanup.

New saturation trials use `trace_z3_v2.py`. It persists each stream chunk and
offset index before forwarding bytes, so a verifier that immediately kills its
solver after the final acknowledgment cannot outrun recording. V1 is retained
unchanged for its frozen earlier experiments. V2 metadata explicitly identifies
`forwarded_ns` as the forwarding-start boundary; query waits still use the
stream-receive boundaries described below. Check V2 with
`Z3_EXE=/absolute/z3 python3 tools/performance/smt/test_trace_v2.py`, including
20 real immediate-kill-after-acknowledgment controls.

`analyze_trace.py CAPTURE_DIRECTORY --output NEW_REPORT.json` checks contiguous
chunk offsets and byte counts, parses quoted SMT expressions/comments and pairs
commands with responses while tracking `print-success`. It retains command byte
offsets/hashes, query responses, response waits, declaration/assertion counts and
quantifier/pattern occurrence counts. Protocol errors remain explicit. Matching
counts do not establish equal formulas, obligations or accumulated contexts.

Response waits start when the relay receives the chunk containing the end of a
command and end when it receives the chunk containing the end of the response.
They include relay/pipe/scheduling costs. Commands sharing a chunk have the same
time boundary; this is not exclusive solver CPU or a count of instantiations.
Multiple solver intervals may overlap; do not sum their wall durations into a
sequential application decomposition.

Run the real transport control with a configured solver:

```sh
Z3_EXE=/absolute/z3 python3 tools/performance/smt/test_trace.py
```

The control compares real direct/relayed version and protocol output byte for
byte, exercises sat/unsat and `print-success` changes, pairs responses, and rejects
truncated SMT and incomplete chunk indexes.

The [nested iterator investigation](../../../porting/performance-nested-smt.md)
records the first use, exact settings, retained transcripts and limits. Its
compressed evidence can be decoded into a new directory and analyzed again.
For solver-only diagnostic replay, its original captured stdin bytes were sent
to a fresh identical Z3, followed by `(get-info :all-statistics)`. The full
original response prefix was checked before interpreting appended statistics.
This follows a fixed recorded path rather than recomputing verifier decisions.
Resource limits remained active. Timing variability and process ownership still
need consideration when interpreting replay results.

`run_saturation.py --spec FROZEN_SPEC.json --output NEW_DIRECTORY` implements the
[comparable saturation protocol](../../../porting/performance-saturation-protocol.md).
It checks artifact hashes, writes the complete schedule first, gates on real
negative controls, captures serial verification trials and audits fixed-path
solver replays. `--prepare-only` prints the schedule without running verifiers.
The spec explicitly supplies commands, inputs/oracles, profiles, CPU affinity,
limits, repetitions and hashes; the runner does not infer a production default.
Run `python3 tools/performance/smt/test_saturation.py` for schedule integrity and
proof/failure/cleanup classification checks.
