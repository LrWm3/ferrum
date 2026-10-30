# Completion sequence after owned continuations

The user requested autonomous work through the first four stages below, in this
order, and subsequently authorized performance testing once comparison is done.
Stage 5 follows completion of the compatibility comparison.
The starting Ferrum checkpoint is `d17ef02`; Prusti integration is `1b994e389`.
Source semantics remain pinned to the revisions in `sources.toml`.

Each implementation chunk must compile, receive focused validation, and be
committed and pushed. Full-source snapshots used for checks must be immutable
during compilation; their complete changed-file manifests must match the admitted
code. A gate cannot be removed merely because a public option can be parsed.
Port gaps remain open until connected and checked; source restrictions and
intentional native API/rendering adaptations must be identified separately.

## 1. Diagnostics and reporting — complete

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

The initial audit found that native debugging was gated and ordinary failure
contexts did not carry the proof obligation required for replay. General logging
implemented levels and ancestry internally, but public activation and event
delivery still needed reconciliation. The historical ADT discriminator outcome
mismatch in `silver/0236.vpr` is carried forward for semantic investigation.

### Earlier checkpoint at `08ff634`

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

### Completed diagnostics/reporting checkpoint

Public native debugging is enabled after source-goal/state capture, joined and
quantified metadata, wand packaging, linked solver settings, and cleanup checks.
The final assembled library run passed all **810 tests** with real Z3 enabled:
21 root-library, 365 Silicon, and 424 Silver tests. A separate **15-test** public
pass covers the debugger, stdio/linked exceptions, statistics, domain logs and
cycle diagnostics. The workspace all-target check passes without the linked
feature, and all workspace targets compile with `native-z3`. Production profiles
remain unchanged. The broader compatibility stage is still ahead.

The manifest-verified diagnostic review has 132 exact line lists, 22 differing
lists, four multiline reviews and 17 unavailable comparisons out of 175 selected
historical cases. Documented rendering adaptations are separate from the semantic
issues and timeouts carried into later stages; none are counted as agreement.
See [the diagnostic review](diagnostic-audit-c51.md) and [debugger/reporting
validation](debugger-validation.md) for scope, commands and reproduced source
limitations. The latter records native EOF/collection presentation, source
simplified-unfold failure, source sequence replay behavior and API solver settings.

## 2. Advanced features and hardening — complete

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

The concrete source gaps are fixed at `f686fde`: generic-domain grounding,
annotated Boolean overloads, failed heap-trigger arguments, termination metadata,
function permission warnings, SIF conditions and structured SIF/ARP diagnostics.
Completed member loggers detach correctly, deep cancellation checks exercise
actual workers and solver reaping, and the demonstrated native stack overflows
have same-thread recursion checkpoints and focused regressions. The exact committed
source passed all 826 library tests with real Z3, no failures and no ignored
tests; see [hardening-validation.md](hardening-validation.md) for checked coverage
and explicit limits. Unexercised unsupported paths remain
unclassified for broader compatibility triage, not silently accepted.

## 3. Fresh Prusti verification — complete

- Update the isolated `prusti-ferrum` integration worktree to the resulting
  committed Ferrum revision; preserve the user's active stdlib worktree.
- Rebuild the native and JVM configurations and run the current iterator/stdlib
  positive and negative fixtures with caches disabled and recorded settings.
- Record exact source revisions, binary hashes, commands, expected obligations
  and outcomes. Compare identical Viper inputs when diagnosing differences;
  independently generated encodings must not be silently treated as identical.
- Fix regressions and rerun affected fixtures. Replace the older matrix in the
  integration validation record with clearly identified fresh evidence.

The fresh integration source is frozen at committed stdlib snapshot
`708b0063c1ebc76521e89291d4fab16e3b63bcc3`, merged with adapter `1b994e389`,
with Ferrum pinned to `f686fde`. The user's uncommitted stdlib work is preserved.
Both locked nightly-2026-08-15 native-only and dual native/JVM builds pass.
The current matrix contains 602 client binaries across eight stdlib suites,
plus spec-library, Rust/runtime and trigger controls. Explicit harness backend
selection is required because inherited `PRUSTI_*` variables are cleared.
The complete initial matrix has 602 clients on each backend, with fixture hashes
and coverage checked: 516 native and 545 JVM annotations match. A corrected map
adapter rerun closes 21 native client differences. The updated integration
`3f623122a` pins Ferrum `5cbb29b`, passes both builds and 17 adapter tests, and
completes every planned original-budget retry. Of 28 iterator client attempts,
12 meet expectations, 11 time out and five retain shared Prusti failures. The
iterator library verifies. Of 12 borrow attempts, eight meet expectations, three
time out and one retains a shared encoder failure. No retry reaches the outer
watchdog or unexpectedly accepts a negative fixture. Remaining timeouts are
inconclusive; this is incremental validation rather than a full matrix rerun on
the final binary. The earlier eight-case matrix is not reused.
The [fresh Prusti validation record](prusti-validation.md) documents the frozen
builds, 602-client inventory, initial results, effective settings and reproduced
source-version differences separately from incremental corrections.

## 4. Broader compatibility testing — complete

The final comparison uses runtime and tooling `afdf10c` against pinned Silicon
`ff386ae` and Silver `c4f54b8`. All 1,512 selected stdio pairs were recorded:
651 both verified, 846 have matching failure IDs and spans, and 15 remain
inconclusive because of timeouts. No conclusive outcome or ID/span mismatch
remains in the selected corpus. Four failed original source sessions and their
32 selected isolated retry sides remain separately recorded.

The linked and two-worker profiles each cover 26 representative cases with
nine shared proofs and 17 matching failures. They have exact message, order,
warning and configuration-warning agreement, plus two documented phase-label
adaptations. Across the full stdio corpus, four prover-warning arrays and 51
reviewed message renderings still differ; four further message comparisons are
inconclusive timeout pairs. The eight remaining phase-label differences are
recorded separately. The focused linked replay also preserves the pinned
source API heap-sort failures and timeout/crash limitations.

Seventeen of 18 lifecycle controls passed. The source stdio timeout-then-valid
control failed with an unknown `Seq<PyType>` sort; all native timeout controls
recovered. Supervisor process reaping succeeded in all controls, while native
backend cleanup warnings remain recorded. These are distinct observations.

The corrected code passed 398 affected linked library tests. Prusti pin
`a59ed917c` passed both locked production configurations and launchers plus all
17 real-Z3 adapter tests. This is incremental integration validation; the
602-client Rust matrix remains the separately recorded stage-3 run.

The [final comparison report](compatibility-final.md) and its machine-readable
companion record coverage, artifacts, exact discrepancies, controls and limits.
The [initial baseline](compatibility-baseline.md), [intermediate dc20 run](compatibility-dc20.md)
and [corrective regression checks](compatibility-corrections.md) preserve earlier
evidence. Both comparison drivers disabled Silicon internal caches. Performance
measurements must distinguish that option from Prusti result caching.

## 5. Performance measurement — in progress

The compatibility review is complete. Measurement tools are being validated;
no performance trial or speed claim has been made at this checkpoint.

Benchmark representative actual Prusti stdlib workloads with
branch parallelism disabled/enabled and different worker counts. Freeze the
validated Ferrum/Prusti revisions, build profiles, dependency binaries, fixtures,
cache settings and timeout budgets. Retain generated Viper inputs so backend
comparisons use the same obligations. Check proof outcomes in every trial;
timeouts remain censored observations rather than successful timings.

Measure fresh-process startup and repeated-session behavior separately, with
repeated trials and recorded execution order. Separate startup, Rust encoding,
frontend preparation, native symbolic execution and Z3 time where instrumentation
supports that distinction. For multiple workers, report elapsed wall time and
aggregate worker/solver time separately: overlapping durations must not be added
or subtracted as if they were sequential phases. Document any unmeasured portion.

Report the measurements, variability and practical limits before recommending
further optimizations. Runtime durations gathered to enforce compatibility-test
watchdogs are not comparative performance evidence.
