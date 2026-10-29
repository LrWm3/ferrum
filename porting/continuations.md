# Native continuation ownership

`--parallelizeBranches` enables owned branch jobs. Combine it with
`--numberOfParallelVerifiers N` to choose the worker count. Even `N = 1` uses
the cooperative queue. Branch parallelism remains off by default.

The native runtime represents the reviewed built-in continuation chains with
typed return frames, exact terminals and identified collectors. A worker can
finish an eligible branch through its caller's expression, rule or CFG suffix.
Jobs carry symbolic data; borrowed closures, live verifiers and solvers stay on
their owner threads. Custom callers without an owned destination execute locally.

This is an ownership and compatibility change. It does not establish a speedup
over JVM Silicon or Verus, or complete the broader Viper port.

## Source baseline

The semantic baseline is Silicon
[`ff386aec4664231dc6f2cb56d8d35f1623088363`](https://github.com/viperproject/silicon/tree/ff386aec4664231dc6f2cb56d8d35f1623088363),
with Silver `c4f54b84703a04434b03e97bfea87dbd09870fd2`. In particular, see
[Executor.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Executor.scala),
[Evaluator.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Evaluator.scala),
[Brancher.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Brancher.scala),
[Consumer.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Consumer.scala),
[Producer.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Producer.scala)
and
[ExecutionFlowController.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/ExecutionFlowController.scala).

## Executable destinations

An owned destination represents the actual callback, never an inferred current
method. Method completion, a single CFG edge, a loop phase and an expression
collector have different return behavior. Local callbacks are still used within
an action, but they are created and completed by the worker running that action.

| Caller | Owned representation |
| --- | --- |
| Method and standalone CFG | Edges, join context, lazy path ID and exact method/standalone terminal |
| Sequences, TryBlock and loop-head statements | Remaining statements and enclosing success/finish frames |
| Complementary CFG guards and individual conditional edges | Guard receiver with the exact edge action and terminal; the owner retains the surrounding edge fold |
| Loop guard wellformedness | Success receiver inside the original local loop scope, discarding the checked value as in the source |
| Inhale, exhale and assert | Projected assertion suffixes, split snapshots, heap completion and caller tail |
| Method preconditions, postconditions and wellformedness | Separate contract/body/success terminals with original scopes and error attribution |
| Method calls | Ordered actual arguments, caller store/heaps, return targets, precondition consumption and postcondition production |
| Fold and Unfold statements | Ordered predicate arguments, permission input, predicate snapshot/body completion and caller restoration |
| Loop invariants | Identified collection outputs, establishment replay and distinct backedge success |
| Local and field assignments | Exact assignment receiver, captured operands and statement suffix |
| Function applications | Ordered arguments and a precondition snapshot receiver returning to the identified expression join |
| Expression Unfolding | Ordered arguments and permission, cached/uncached predicate body completion, restored state and expression body |
| Applying expressions | Wand, LHS and RHS completion stages, restored old heaps/store and body result collector |
| Quantified evaluation | Ordered body values/debug options, trigger completion and exact local quantified collector |
| Production and consumption subexpressions | Guard, pure assertion, access-argument/permission and impure Let receivers retaining enclosing rule frames |

Expression return frames compose around Asserting, Let, old/labelled-old, field
reads, Boolean and arithmetic/permission operators, conditional and short-circuit
expressions, function/domain/backend arguments, collection constructors and
operations, CurrentPerm and ForPerm resource arguments. Each frame retains the
source evaluation order and shares ordinary term/debug completion where possible.
SeqContains evaluates its sequence before its element. Ordered argument debug
options use the same reverse fold as the ordinary evaluator.

Wand arguments are the exact ordered holes selected by the source wand helper.
The owned path resolves those holes before changing evaluation state. An
Asserting expression elsewhere in a wand must not be evaluated merely because a
conservative syntax probe found it. Unfolding's recursive cutoff likewise occurs
before argument or permission evaluation.

Return frames are stored outermost first and resumed from the end. An iterative
probe selects a supported descent path, avoiding repeated suffix scans and front
insertion. Evaluation itself remains recursive and some suffix transitions clone
frames; this is not a general linear-time or stack-safety guarantee.

## Collector, solver and cleanup ownership

Expression joins, quantified results and loop-phase results have distinct
collector destinations. Nested rule receivers discover their destination through
their saved continuation frames. Worker execution installs the matching local
collector identity and restores the suspended collector afterward. Returned
declarations are replayed before values or phase results are consumed.

Each solver remains on its owning thread. Jobs capture immutable path,
declaration, option and error-count snapshots before the local then branch
starts. A cooperative wait can execute an unrelated job on the same worker;
worker identity alone therefore cannot prove that its solver has the right state.
The suspended solver and path context must be restored before its caller resumes.

Terminal jobs return verification results and warnings without creating expression
join entries or replaying parent solver effects. Value and phase jobs return their
distinct owned outputs. The waiting caller retains its local scopes, source result
combination and cleanup. Submitted sibling jobs are drained even when the local
branch, reporter or continuation fails.

Consumption retry frames distinguish entry into a successful continuation from
failure in its subsequent tail. A downstream failure must not retry successful
consumption. Pure assertion consumption retains both inner and outer retry
boundaries. Heap/reserve restoration, constrainable permission restoration,
snapshot completion and scope closing occur at their original success boundaries.
Synchronous retries keep ordinary local state and avoid the shared success signal.

Typed cancellation and context/service/solver errors survive the reviewed rule
adapters. A callback-abort sentinel preserves the original failure, and independent
cleanup failures remain visible. An actual failed solver pop is not established
to be recoverable by the injected cleanup-error tests. A panic aborts verification:
pending work is cancelled and the affected worker is stopped rather than reused.

Every owned subtree entry rechecks its runtime guards. If an earlier local
operand changes eligibility, later evaluation stays synchronous and then resumes
the saved return frames. No receiver may bypass packaging, extended-exhale,
logging or source join restrictions.

## Deliberate synchronous boundaries

Several local paths are source semantics or explicit API boundaries:

- Direct evaluator branches and joined producer/consumer forks explicitly disable
  parallelism upstream. Nested rules may restore the original flag; those nested
  continuations can use their owned receivers. Function/predicate verification
  starts with parallel branches disabled, while methods and standalone CFGs opt in.
- Wand proof packaging and extended exhale retain their source restrictions.
  Applying LHS/RHS conditional stages transfer only in the source-eligible join
  mode; an all-joins control must not manufacture a job.
- Generic borrowed callbacks and unimplemented extension evaluator interfaces are
  not converted into executable jobs by guessing a terminal.
- Active member logs retain the safe local fallback. Public advanced logging
  (`--ideModeAdvanced`) or state reporting (`--reportStateAfter`) combined with
  parallel branches is rejected by the pinned source configuration and by Ferrum.
  Reused standalone CFG contexts can retain a previous member logger; general
  logger migration for this internal embedding case is not claimed complete.
- First-stage quantified-condition evaluation retains its ordinary local callback.
  A tested independent two-path Asserting condition aborts the pinned serial Scala
  local-Q cardinality assertion; the native path rejects multiple local results.
  Constraining the condition removes the sibling branch. This is not evidence for
  a source-valid missing transfer. Second-stage permission/resource body results
  use the identified quantified receiver.

Source join cardinality is preserved. A nested two-way Asserting plus another
outer branch can produce three entries where the pinned serial source accepts
only one or two. Positive join fixtures constrain the outer condition and retain
the independent inner branch. Short-circuit joins skip feasibility filtering;
their nested-tail tests establish actual jobs and the expected invalid-entry
error, not successful verification of that source-invalid shape. A parallel Scala
run that races a local collector is not a reliable replacement for serial source
semantics.

## Validation and its limits

Real stdio Z3 fixtures run with one and two workers and assert actual submissions
and executions, independently of successful verification. They cover receiver
values, resource preservation, first/later argument stages, failure ordering and
skipped caller tails. CLI controls retain source error categories and default or
unlimited error-reporting behavior. Selected positives and negatives are compared
with the pinned sequential Scala reference.

Cancellation probes stop work after receiver entry or sibling submission and
check typed cancellation and pool draining. They distinguish right operands,
nested Asserting, Let, Boolean heads/tails, joined/quantified values, CFG guards,
loop guard checks, ForPerm, wand arguments, Unfolding inputs and Applying stages.
These probes do not prove simultaneous parent/child execution at every hook.
The loop guard probe has its own hook and fixture; the CFG guard probe is not a
substitute for it.

Deterministic scheduling tests separately force foreign-worker replay and
same-worker execution of unrelated collectors and methods. They check parent
solver depth, path layers, options, error counts and collector restoration.
Negative controls that remove restoration fail. Queue/reporter and paired error
tests exercise draining and retention of independent failures.

Coverage qualifications:

- The individual conditional-edge test replaces a method's CFG while retaining
  its normal preamble. It covers true, false and later-edge behavior with actual
  jobs; it is not a claim that a source-generated single-edge fixture transferred.
- The source-valid ForPerm argument transfer fixture uses a predicate resource;
  Silver requires a field resource's bound receiver directly.
- Dedicated local debug/trigger comparisons for Let and old-state returns use
  an injected scheduler. Separate fixtures establish real worker transfers;
  they do not establish every debug profile under transfer.
- Active advanced logs plus branch parallelism have configuration rejection
  tests, not an invented parallel trace protocol.
- Mask alias replay is checked through stdio and linked Z3 4.16 with one/two
  workers. Available aliases are tracked per solver; self/forward aliases are
  excluded and restart/failure clears stale availability. Required global
  declarations cannot be disabled through startup or member options.
- Warning tests preserve evaluator wording, source positions, reporter category,
  occurrence order and reporter failures, including missing quantified triggers.
  This does not establish complete diagnostic formatting parity.

Run real-solver tests with `FERRUM_TEST_Z3` explicitly set; some library fixtures
skip their solver work otherwise. Compile outside the external runtime watchdog,
then run cancellation tests with a bounded process timeout. Serialize tests that
share stage counters. Production development builds retain optimization level 1
for the recursive verification crates; test-only level-0 overrides are useful for
focused build turnaround but are not the Prusti execution profile.

See [README.md](README.md) for checkpoint results and the wider compatibility
inventory. The Prusti adapter's `prusti-ferrum/VALIDATION.md` distinguishes current
build checks from its older Rust iterator matrix. Neither record should be read
as an end-to-end performance comparison.
