# Completion sequence after owned continuations

The user requested autonomous work through the first four stages below, in this
order. Performance measurement is a later stage and is not part of this run.
The starting Ferrum checkpoint is `d17ef02`; Prusti integration is `1b994e389`.
Source semantics remain pinned to the revisions in `sources.toml`.

Each implementation chunk must compile, receive focused validation, and be
committed and pushed. Full-source snapshots used for checks must be immutable
during compilation; their complete changed-file manifests must match the admitted
code. A gate cannot be removed merely because a public option can be parsed.
Port gaps remain open until connected and checked; source restrictions and
intentional native API/rendering adaptations must be identified separately.

## 1. Diagnostics and reporting — in progress

- Reconcile source messages and positions, including the outstanding termination
  clause spans and collection-expression parentheses in the earlier diagnostic
  comparison. Review comparisons that the old output parser could not classify.
- Complete general log levels, named overrides and source event delivery. Keep
  verbose modes gated while required events or renderers remain missing.
- Connect interactive debugging: capture the failed assertion, symbolic state,
  assumptions, declarations and preamble before scope cleanup; replay into an
  owned solver; connect debug parsing/typechecking/evaluation and the source
  command protocol. Retain source configuration restrictions.
- Validate success/failure ordering, reporter errors, positions, repeated runs
  and meaningful scripted debugger sessions against the pinned source where
  applicable. Document deliberate formatting differences explicitly.

Initial audit found that native debugging is still gated and ordinary failure
contexts do not carry the proof obligation required for replay. General logging
already implements levels and ancestry internally, but public activation and
event parity still need reconciliation. The historical ADT discriminator outcome
mismatch in `silver/0236.vpr` is carried forward for semantic investigation.

### Checked progress through `08ff634`

Failure contexts now carry detached proof obligations, retained source scopes,
declarations, assumptions and predicate/function registries. Owner-thread stream
sessions provide input checking, presentation, replay, solver replacement and
explicit cleanup. The integrated Silicon suite passes all 317 tests with real
Z3 enabled, including 20 debugger tests. These cover quantified field reads and
assignments, negative permissions, wildcard consumption, allocation and replay
after the original verifier is dropped. A two-worker pool shutdown/replay test
also passes; it does not assert which branch executed on which worker.

Three public CLI/stream regressions pass in an isolated test build with the
configuration gate bypassed. They cover successful programs, multiple failures,
invalid input, EOF, independent sessions and solver reaping after an output error.
The production gate remains closed while joined-value/heap-trigger metadata,
linked-solver replay and remaining exception/reporting paths are completed.

The integrated Silver suite passes 415 tests at this checkpoint. Diagnostic work
now covers parser recovery, macro positions, sibling error collection, contextual
identifiers and parser-only types. `tools/compare_diagnostics.py` verifies reference
fixture/jar hashes, handles padded error indices and preserves raw evidence.
Multiline messages, unsupported paths, crashes and timeouts require review; equal
failure exits are not agreement. The final integrated diagnostic comparison is
still pending. Later stages below remain pending, and no performance claim is
made from these checks.

## 2. Advanced features and hardening — pending

- Audit reachable unsupported extension/configuration paths against the source
  and connect missing native services; keep genuine source restrictions explicit.
- Resolve internal member-logger ownership/reuse without enabling combinations
  the pinned source rejects. Public advanced logs plus parallel branches remain
  a source-invalid configuration.
- Investigate recursive stack usage on representative and deep inputs. Retain
  production optimization settings while fixing actual overflow paths; a larger
  stack alone is not evidence of a bound.
- Exercise cancellation, worker interleaving, collector isolation, cleanup errors
  and session reuse in the newly connected paths. Check failure behavior as well
  as successful transfers.

## 3. Fresh Prusti verification — pending

- Update the isolated `prusti-ferrum` integration worktree to the resulting
  committed Ferrum revision; preserve the user's active stdlib worktree.
- Rebuild the native and JVM configurations and run the current iterator/stdlib
  positive and negative fixtures with caches disabled and recorded settings.
- Record exact source revisions, binary hashes, commands, expected obligations
  and outcomes. Compare identical Viper inputs when diagnosing differences;
  independently generated encodings must not be silently treated as identical.
- Fix regressions and rerun affected fixtures. Replace the older matrix in the
  integration validation record with clearly identified fresh evidence.

## 4. Broader compatibility testing — pending

- Run a reproducible selected corpus against native Ferrum and pinned Silicon,
  including ordinary and advanced features, valid and invalid obligations,
  multiple workers, timeouts, reset/reuse, and both available solver transports.
- Triage every discrepancy. Equal nonzero exit codes are insufficient to show
  compatible failures; source crashes and harness timeouts are inconclusive.
- Investigate unexpected native success before accepting a result, fix confirmed
  port defects and retain reduced permanent regressions.
- Publish the final matrix, commands, coverage and individually justified
  source/API limitations. Report unresolved port defects as unresolved rather
  than declaring this stage complete.

## 5. Performance measurement — deferred

After the requested stopping point, benchmark representative stdlib workloads
with branch parallelism disabled/enabled and different worker counts. Separate
startup, Rust encoding, native symbolic execution and solver time before choosing
further optimizations. Runtime durations gathered to enforce test watchdogs are
not comparative performance evidence.
