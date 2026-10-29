# Native debugger and reporting validation

This closes the diagnostics/reporting work before the advanced-feature and
hardening pass. It does not establish complete Viper compatibility or a speedup.
The semantic references remain Silicon `ff386aec4664231dc6f2cb56d8d35f1623088363`
and Silver `c4f54b84703a04434b03e97bfea87dbd09870fd2` in `sources.toml`.

## Connected behavior

`--enableDebugging` now uses the public native frontend and stream session.
Failure records retain the assertion term, source expression, symbolic state,
assumptions, preamble/declarations, recorded heaps, and function/predicate
registries before solver cleanup. The original verifier can stop before replay.
Solvers stay on their owner threads; detached failure data crosses worker result
channels. Source restrictions on mask heaps and advanced logging with parallel
branches remain enforced.

Tests cover function/field evaluation, permissions and allocation, quantified
reads and writes, resource triggers and snapshot definitions, actual multi-entry
unfolding/applying joins, packaged wands, division, sequence bounds and map keys.
Joined-value tests check guarded equations and feasible branches, resolve recorded
heap labels, and replay the resulting failure. The public tests exercise invalid
input, multiple failure selection, EOF, output errors, independent sessions,
advanced reporting, and two-worker stdio/linked configurations. These checks do
not establish deterministic execution on distinct branch workers; that is part of
the hardening pass.

Linked-Z3 replay records the effective accepted typed solver options and the
actual randomized seed, preserving their applied order. Unknown options retain
the source warning-and-skip behavior; they are not replayed. A fresh Z3 process
receives its static settings, then the journal, before axioms and assumptions.
Supported SMT-LIB option spellings are probed and responses are drained through
an echo marker because stdout/stderr share a protocol stream. An unmappable key,
unrepresentable value, or Z3-specific settings with cvc5 produce explicit errors.
They are never silently dropped. Tests include Boolean/double/global-timeout
settings and signed-to-unsigned seed conversion followed by randomization.

General logger levels/overrides, prover comments and events, domain-trigger logs,
source exception reporting, and catching-policy behavior are connected. Reporter
or cleanup errors remain visible alongside the original failure. Actual native
error messages/backtraces replace JVM-specific stack representations. Startup
configuration confirmations precede entity results, as checked by the direct
session reporter test. Retained postcondition axioms survive session reset for
execution-trace reporting.

## Bounded source audit

The reviewed failure families include Consumer.scala:433, Executor.scala:505,
Evaluator.scala:779/963/1013/1020/1221, HeapSupporter.scala:418/469, quantified
negative permissions, and the source description-only failure overloads in
ChunkSupporter, QuantifiedChunkSupport and MoreCompleteExhaleSupporter.

Assumption review covers ordinary chunk constraints, generated expression goals,
quantifier auxiliary groups, quantified summaries/triggers, cached predicate-body
assumptions, source-named wand/havoc/alias definitions, and named prover preamble
axioms. Joiner.scala:94–113 and Evaluator.scala's value join supply branch
conditions, value equations and StateMerge recording. Raw/direct decider calls
remaining without debug expressions are non-debug branches, source-invalid mask
combinations, or the reproduced source limitation below. This is a bounded
callsite and fixture audit, not a proof of every option combination or renderer.

## Reproduced source behavior and native boundaries

- A failed sequence-bound check can replay as PASS. Pinned Evaluator.scala
  assumes the bounds while continuing after an error, then captures the failure.
  The source interactive probe retains `i >= 0` among its assumptions while that
  is also its failed goal. Native capture and replay preserve this behavior.
- Debugging with `--enableSimplifiedUnfolds` can reach a cached predicate leaf
  whose nonquantified field chunk becomes quantified. PredicateSupporter.scala:121
  calls `assumeDefinition(..., None)`; source Decider.scala:322 aborts on `None.get`.
  Native returns `Decider(MissingDebugExpression)` at the corresponding definition.
  With ordinary unfolding, the same fixture verifies through the public CLI.
- Source reset retains its mutated initial worker. The tested command sequence
  prove/add-assumption/prove/reset/prove/replace-solver/prove yields
  FAIL/PASS/PASS/FAIL, followed by FAIL in an independent replay.
- Native EOF exits and reaps solvers; the source readLine path can throw/retry on
  null. Debugger sequences use canonical `List(...)` because Scala collection
  implementation classes are erased. Programmatic ASTs without a retained parser
  program cannot resolve scoped textual debugger input.
- The pinned Java-API debugger stalled during initialization in bounded probes.
  The working native API-to-stdio replay is an explicit extension; those source
  timeouts do not establish transcript parity. cvc5 replacement is untested in
  this environment because the executable is unavailable.

The simplified-unfold witness is:

```viper
field f: Int
predicate P(x: Ref) { acc(x.f) }
method m(x: Ref, s: Set[Ref])
  requires acc(P(x))
  requires forall y: Ref :: y in s ==> acc(y.f)
{
  assert (unfolding acc(P(x)) in true)
}
```

## Validation evidence

The isolated assembled tree includes the final diagnostic fixes, metadata paths,
effective API settings, and public activation. All-target checking passes without
the linked feature; the full workspace compiles with `native-z3`. Runtime checks
use the pinned linked Z3 4.16 library and the configured real stdio Z3 executable,
with test-only optimization overrides of zero for all three Ferrum crates.
Production optimization settings remain unchanged.

The final library run and selected public integrations are recorded in
`/tmp/ferrum-root-stage1-final-library-2.log` and
`/tmp/ferrum-root-stage1-final-public.log`; aggregate counts are recorded in
`completion.md`. The earlier workspace regular-test run passed 765 tests with 194
ignored. The public integrations cover debugger sessions, exceptions, statistics,
the domain log event and cycle diagnostics. Compilation is completed before the
runtime watchdog; serial test ordering avoids shared test-counter interference.

The diagnostic comparison is recorded separately in `diagnostic-audit-c51.md`:
132 exact line lists, 22 differing lists, four multiline reviews and 17 unavailable
comparisons among 175 selected historical cases. Source timeouts and semantic gaps
remain open for the next stages. Same nonzero exit status is never treated as
proof or diagnostic agreement. No performance conclusion follows from these runs.
