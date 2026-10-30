# Compatibility session evidence

`SourceSession.java` uses the pinned source jar, creates and prepares one
Silicon frontend, then resets, parses, translates and verifies each path in
order before stopping the verifier. It emits `@@COMPAT@@` JSON with actual
`AbstractError.fullId`, `pos`, and `readableMessage`, and the reached frontend
phase. Exceptions remain exceptions. Raw frontend/plugin output is retained.
The native example uses one Ferrum `Session` and a fresh frontend per input,
maps verification results, transforms errors, applies plugin finish hooks and
deduplicates before stopping the session. Source invokes its frontend finish
for verification results; frontend errors remain separately reported. Both
capture warning events per case. Focused refute, termination, SIF and ARP
controls matched error IDs and positions, but do not establish general parity.

Compile against source jar SHA bcab94591994788e41a62fa673f1001339ac2323ef58e27d428a7ca739c12726:

```
mkdir -p /tmp/source-session-classes
/tmp/ferrum-jdk17/bin/javac -cp /tmp/ferrum-reference-silicon/target/scala-2.13/silicon.jar -d /tmp/source-session-classes tools/compatibility/SourceSession.java
python3 tools/compatibility/run_session.py --timeout 120 --output source.json -- /tmp/ferrum-jdk17/bin/java -Xss128m -cp /tmp/source-session-classes:/tmp/ferrum-reference-silicon/target/scala-2.13/silicon.jar SourceSession Z3_PATH --timeout 30 -- pass.vpr fail.vpr pass.vpr
```

Build an immutable repository snapshot with `cargo build --locked --example
compatibility_session` and a distinct `CARGO_TARGET_DIR`. Invoke the resulting
example with the same Z3 path, shared options, `--` separator and files using
`run_session.py`. Both drivers use Z3 and disable caches. They add a one-worker
default only when the caller supplies no `--numberOfParallelVerifiers` option;
the split and `=value` forms are supported. Caller arguments are retained in
order, including duplicates. The pinned source rejects duplicate worker options;
the native config currently takes the last value, so do not use duplicates for
paired runs. Source exceptions and unknown
result variants stop the session; recovery after exceptions is not asserted.

The tooling was checked and built over `dc2b014`, whose backend code is
`f686fde563e0e971d20a46eb8dd14e083a11e801`. The final drivers both completed a
reused session containing success, assertion failure, parser failure and success,
with matching error IDs and positions. Five evidence-classification tests and
five subprocess/cleanup tests pass. This establishes the focused harness checks;
the broader corpus run remains pending. Rebuild against the final frozen backend
revision before that run. Hash the
source driver, compiled class, native executable, Java, jar, Z3 and fixtures.
`compatibility_evidence.py freeze` hashes source repositories and binary inputs;
review imports outside those roots independently. A killed process is recorded
as `harness_timeout`, not an error ID or matching failure. The runner bounds
and kills its own process group; this is a Linux/Unix runner.

Include SIF and ARP regression directories explicitly: the older `compare_upstream.py` suite list omits them. Match source and native plugin flags, retain frontend failures separately, and compare IDs and positions only when actually emitted.

`compatibility_evidence.py compare` accepts observation pairs whose source and
native objects include `session_outcome` and `exit_code` copied from their
containing runner result. It requires completed, zero-exit sessions, and its
`same_ids_positions` label compares only the error ID/position multiset; it does
not claim matching messages, warning arrays, phase, or ordering. Compare those
fields separately. A `timeout.error` always remains inconclusive, even when a
producer leaves its row labelled failure. Supply `--artifact` for class files,
linked libraries and imported files outside the hashed source trees; git status
is recorded so dirty reference checkouts are visible. Source JAR identity
covers built-in imported resources, not arbitrary external file loaders.

On Linux the standalone runner enables child-subreaping, samples process
ancestry with PID and start-time identities, and discovers adopted children after
the leader exits. It kills and reaps observed or adopted descendants, including
children that create a new session. A bounded cleanup failure is reported as
`process_error` with the pending identities. The timeout path also signals the
owned session process group. Processes that escape the runner's ancestry through
an external process manager remain outside this guarantee. Session reuse stops
on exceptions; these are not verification results. `process_error` also covers
malformed protocol records and unknown or unrenderable outcomes. On non-Linux
ancestry tracking is unavailable; the group timeout remains Unix-specific.

## Corpus selection and execution

`corpus.py` selects the original 1,190 `.vpr` cases plus SIF, ARP, ADT,
quasihavoc, greedy/complete exhale, conditional permissions, old permissions,
old axioms, simplified unfolds, parallel examples and mask-heap configurations.
The complete selection has 1,512 fixture/configuration combinations. The named
upstream test classes supply directories and flags. `.sil` files are excluded;
annotations, including ignores and missing outputs, are retained as metadata
without suppressing cases or pretending to implement ScalaTest's evaluator.

```
python3 tools/compatibility/corpus.py --silver SILVER_ROOT --silicon SILICON_ROOT --output selection.json
```

Freeze executable, jar, Java, Z3 and source resource hashes with
`compatibility_evidence.py freeze`. Use repeated `--artifact` arguments for both
compiled Java classes, linked solver libraries and any external imports. Build
and run from immutable snapshots. A settings JSON file supplies `source` and
`native` command-prefix arrays, each ending with the Z3 path, `shared_options`
(for example `["--timeout", "30"]`), optional `environment` overrides, and
`command_artifacts` with explicit `source` and `native` path lists. The latter
must name dynamic libraries and external imports that command-file discovery
cannot infer. A typical source prefix is the Java executable, `-Xss128m`, `-cp`,
the class-directory/JAR classpath, `SourceSession`, and the Z3 executable; the
native prefix is the built example and the same Z3 executable.

```
python3 tools/compatibility/run_corpus.py --selection selection.json --settings settings.json --evidence evidence.json --tools tools --output RESULTS --jobs 2 --batch-size 8
```

The runner checks artifact hashes, repository revisions/status and the complete
resource inventory before execution. Every session retains raw output and
structured results. Missing, duplicate or out-of-order case records invalidate
the session. Failed batches receive isolated retries while preserving the
original failure. Pair records distinguish completed batches, isolated retries
and incomplete batches; successful retries do not establish successful reuse.
Messages, warnings and phase comparisons remain separate from outcome/error-ID
comparison. Unexpected worker exceptions become incomplete observations and
retain their tracebacks, rather than aborting the remaining corpus silently.
Any pair containing a verifier timeout is inconclusive even when the other
backend completes a proof or reports an ordinary verification failure. Its raw
outcomes remain available for follow-up; it is not counted as a semantic mismatch.

A separate supervisor bounds each session runner, adopts its descendants on
Linux and records its own cleanup evidence. If that supervisor itself fails to
respond, an emergency process-group kill records a runner error; detached
descendants may survive this exceptional path. Six orchestration checks exercise
record coverage, malformed envelopes, retry accounting, reporting differences,
artifact binding and addition of an ignored source resource. The corpus itself
has not yet been run at this checkpoint.

The source worker-option checks use the pinned jar and do not start a solver:

```sh
mkdir -p /tmp/ferrum-worker-config-classes
/tmp/ferrum-jdk17/bin/javac -cp /tmp/ferrum-reference-silicon/target/scala-2.13/silicon.jar -d /tmp/ferrum-worker-config-classes tools/compatibility/SourceSession.java tools/compatibility/WorkerConfigTest.java
/tmp/ferrum-jdk17/bin/java -cp /tmp/ferrum-worker-config-classes:/tmp/ferrum-reference-silicon/target/scala-2.13/silicon.jar WorkerConfigTest tests/fixtures/termination_function_spec_order.vpr
```

The broad `parallel_examples` group supplies `--parallelizeBranches` and an
explicit two-worker option; shared corpus settings must not duplicate it. A
separate targeted two-worker profile should also enable branch parallelism.

Prover interaction, external tool, exceptional and missing-dependency error IDs
are infrastructure faults, not proof failures. The session retains their raw
records, is marked unsuccessful, and a failed reused batch receives isolated
retries; its original session evidence remains visible.
