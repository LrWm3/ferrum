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
`run_session.py`. Both drivers use Z3, cache-disabled, one-worker defaults;
subsequent shared flags may override the latter. Source exceptions and unknown
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
