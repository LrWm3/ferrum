# Native continuation ownership

The native runtime now accepts `--parallelizeBranches`. Combine it with
`--numberOfParallelVerifiers N` to select the worker count. Even `N = 1` uses the
cooperative queue when branch parallelism is requested. The default remains off.
Owned continuations remove the former blanket restriction on transferring
nonjoined branches; callbacks without an explicit owned receiver remain local.

Method and standalone CFG execution now carry an explicit owned terminal alongside
local callbacks. A scheduled CFG action owns its edge, join context, lazy path ID
and terminal. A worker executes the suffix through method postcondition checking
or standalone success. No borrowed closure, live verifier or solver is sent to
another thread.

The source references are Silicon's pinned [Executor.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Executor.scala),
[Brancher.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Brancher.scala),
[ExecutionFlowController.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/ExecutionFlowController.scala)
and [MethodSupporter.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/MethodSupporter.scala).

## Executable boundary

The terminal is propagated only where it represents the actual continuation.
It is not inferred from the current method: join collectors, invariant-phase
collectors and wand proof CFGs can have different continuations. Generic callers
that supply a borrowed callback retain synchronous execution.

Statements, evaluation, production, consumption and retries may still use local
callbacks. Those callbacks are created and completed on the worker executing the
owned action. Multiple invocations retain the source semantics. The waiting
caller retains its own scopes, result combinations and final cleanup. It drains
a submitted else job even when the then action or branch reporter fails.

Joined CFG and predicate actions return owned entries and declarations. Terminal
CFG actions instead return verification results and warnings, never join entries
or parent solver effects. They do not allocate a join mark. Method terminal
errors and cancellation retain their typed representation across the queue.

Direct CFG inhale statements now supply an owned caller frame containing the
remaining statement sequence, block successor and terminal. Producer actions
carry projected assertion suffixes, split snapshots and errors. A transferred
conditional or implication completes its branch and pending assertions before
inhale saturation, statement completion and the caller tail. Implication false
branches retain the empty-snapshot assumption. The same terminal-job scheduler
handles CFG and producer actions, preserving typed native errors.

Direct CFG exhale and ordinary assert statements also have owned consumption
frames. Each frame retains remaining projected conjuncts, their errors, heap
completion and the exact retry attempt. A shared success signal records entry
into the consumed assertion's continuation before later work runs. This prevents
a failure in the tail from incorrectly retrying successful consumption. Retry
frames restore the source retry level/modes and close the retry scope at the
original success boundary. Assert completion restores the original heap and
reserve heaps before resuming the statement tail. Ordinary synchronous retries
retain their local Boolean and do not allocate a shared signal.

Method postcondition consumption has a separate explicit success terminal. Only
`complete_method_cfg` selects it; generic postcondition callbacks remain local.
It preserves per-postcondition error attribution and heap completion without
running statement cleanup. A fixture whose only conditional is in its ensures
clause checks real consumer job execution and an else-only permission failure.

Nested statement sequences and TryBlock bodies have explicit enclosing finish
frames. TryBlock records success before running its caller, so downstream failure
cannot incorrectly trigger fallback; unsuccessful bodies resume from the original
state. Loop-head statements carry their own successor checks before following
edges. Producer and consumer lets retain the source store extension and remaining
assertion/retry frames. Success-only scope closes are represented explicitly;
active logger transfer is still disabled. Ordinary execution without an eligible
scheduler does not construct these statement tails.

Method precondition production now carries the exact method body and CFG terminal.
Disable-subsumption assertion probes have an explicit consumption-success terminal.
The owner waits for the probe result, then resumes the original unconsumed state
once. Real-Z3 checks exercise actual jobs with one/two workers, retained permissions
and an expected downstream failure.

Postcondition wellformedness has its own success terminal in the original local
empty-heap scope. Contract saturation, old-heap recording, fatal-result gating
and separate body verification retain their source ordering. Actual Z3 checks
exercise precondition-only and wellformedness-only forks with one and two workers.

Method calls carry caller stores, heaps, old heaps and return targets through
precondition consumption and postcondition production. Snapshot-returning
consumption now preserves conjunct combination and finalization order. Fold
bodies use that snapshot to rebuild the predicate chunk, restore permission
scaling and resume their statement tail. Real Z3 checks assert actual call and
fold jobs, caller value restoration and an else-only missing-permission failure.

Ordinary unfold statements now retain an explicit finish frame through cached
predicate trees or uncached body production. Both paths restore the caller store
and permission scaling after saturation and trigger emission, then execute the
statement tail. Separate actual-job tests exercise both profiles with real Z3,
checking field values, permissions and an expected invalid value assertion.

## Solver ownership and restoration

Each solver remains on its owning thread. Jobs carry symbolic state and immutable
path, declaration, option and error-count snapshots captured before the then
branch starts. A worker installs the captured context for transferred execution
and restores the suspended context before resuming other work. Nested cooperative
waits require isolation even when a queued action originated on the same worker:
that worker can currently be suspended inside a different branch or loop scope.
Worker identity alone cannot establish that the live solver matches a job.

The regression suite uses actual Z3 with one and two workers, including nested
branches, permission consumption, method postconditions, two fatal branches and
unrelated queued methods. Forced foreign-worker tests check both replay and
restoration; removing restoration makes the negative control fail. An injected
scheduler checks mandatory draining after execution and reporter errors.
A deterministic evaluation test also forces unrelated collector IDs onto the same
worker, checks returned values and parent collector/PCS restoration, and cancels
an in-flight evaluation job. Cancellation tests cover an in-flight terminal job and cancellation of the then
action after else submission, retaining typed cancellation and restoring parent
solver depth and options before return.

## Loop and expression continuations

Loop invariant collection uses explicit collector identities and owned phase outputs. Establishment resumes
phase replay inside its original consumption continuation, retaining retry and
result-combination boundaries. Backedges have a distinct success terminal.
Actual Z3 tests exercise all three phases, including nested invariants and entry
or preservation failures. A deterministic cooperative test checks collector and
solver restoration when an unrelated phase job executes on the same worker.
Disabled scheduling does not allocate or clone the new establishment frame.

Cached and uncached expression Unfolding now carry an explicit value-producing
frame through predicate-tree and producer jobs. Each leaf restores the source
store, recorder depth, scaling and cycle state, evaluates the expression body,
and returns state/term/debug/path data to the original identified join collector.
The owner replays declarations before merging returned entries. Real Z3 checks
exercise both profiles and reject the expected bad postcondition while preserving
the predicate resource and valid branch values.

Function application preconditions now carry an owned snapshot receiver. It
retains trigger rewriting, error substitution, caller-store transformation and
function-recorder restoration before returning the term to its identified join.
Actual Z3 tests exercise conditional precondition jobs and the expected bad
application while checking returned values. A direct local assignment with an
Asserting RHS also owns its state/value receiver: it restores the assertion
heap, evaluates the body, restores the outer evaluation heap/reserves and
performs SSA assignment before resuming the statement tail. A direct old or
labelled-old wrapper around that Asserting RHS retains an owned old-state frame.
Its return restores the partial heap, trigger map and old-state flag in source
order before restoring the outer evaluation heap and assigning. Real jobs check
historical values, current resources, missing labels and an else-only permission
failure. Injected service errors and cancellation after submission check
draining and parent solver restoration. A real worker is also cancelled after
the old receiver starts, at a nested assertion checkpoint. Evaluation,
production and consumption adapters preserve direct typed context errors,
including function-precondition and ordinary assertion-tail checkpoints.
Execution adapters now preserve direct context/service errors as well. Saved
callback adapters recognize a typed continuation-abort sentinel and retain any
independent cleanup error together with the callback failure. Reviewed quantified retry, summary, merge, mask and wand adapters now retain
their nested service/solver errors too.
Nested arbitrary expression callbacks without an explicit receiver remain
synchronous. Active member logging, packaging and extended exhale still disable
owned dispatch. Generic borrowed callback entry points remain local; parallelism
is enabled only where an exact owned terminal or collector represents Q. Direct
evaluator branches explicitly disable parallelism upstream and keep that
behavior.

Packaging proof scripts and joined consumer branches explicitly disable branch
parallelism upstream (MagicWandSupporter.scala and Consumer.scala). Their local
execution is source behavior; the outer statement continuation must still resume
correctly afterward.

Moving captured fields into a struct alone is insufficient. New dispatch points
must identify the exact executable continuation, preserve source result order,
and demonstrate restoration on success, verification failure, service error and
cancellation before removing their guard.

## Coverage and compatibility boundaries

| Caller or context | Current execution |
| --- | --- |
| Method/standalone CFG, sequences, TryBlock, loop heads and successors | Owned actions through exact method or standalone terminals |
| Inhale/exhale/assert (including disable-subsumption probes), method/call contracts, fold snapshots and statement unfold | Owned rule and caller frames |
| Loop collection, establishment and backedges | Identified phase outputs and explicit consumption terminals |
| Function preconditions and cached/uncached expression Unfolding | Owned snapshot/value receivers and identified join outputs |
| Local assignment with Let, old/labelled-old, negation, addition, subtraction, multiplication, equality, inequality and ordered comparisons around Asserting | Composable owned return frames; both eligible strict operands can transfer |
| Arbitrary nested value callbacks, other old-expression shapes and custom borrowed entry points | Safe synchronous fallback; not complete parallel source coverage |
| Active member logs, extended exhale and packaging | Owned dispatch disabled; logger migration remains unfinished |

Upstream explicitly disables direct evaluator and joined producer/consumer forks.
Nested rules can re-enable the original branch flag; some such nested callbacks
still use synchronous fallback. Function/predicate verification begins with
parallel branches disabled upstream; methods and standalone CFGs opt in in
`DefaultMainVerifier.scala`. These source constraints differ from the incomplete
owned-receiver coverage listed above.

All submitted jobs are drained on normal error and cancellation paths. A panic
instead aborts the verification run: the pool cancels pending work and stops the
affected worker, which is not restored for reuse. Public CLI and Session checks
cover one, two and four workers with the flag both off and on through stdio and
linked Z3, including invalid programs, reuse and stop. Internal real-Z3 fixtures
assert actual submissions/executions; deterministic tests force foreign and
same-worker interleaving and cancellation. This establishes the tested ownership
boundaries, not complete Viper compatibility or a measured speedup.

## Cancellation regression boundaries

Real worker probes cancel owned assertion/old jobs after transfer installation,
and an old assignment receiver after its entry hook reaches a nested assertion.
They check typed cancellation, draining, normalized solver depth, path layers,
options and error counts. Queue cancellation is registered; the ordinary probe
uses a cooperative latch to keep the solver available for restoration checks.
The test releases rendezvous and interrupts solvers on its failure path. Run the
regression under an external process watchdog to bound noncooperative CPU stalls.

Deterministic scheduler tests exercise both branch combiners: simultaneous
cancellation remains typed only when restoration and reporting succeed, while a
distinct child or cleanup error remains visible. They also cover a stopped queue
at submission with and without a latched cancellation. These do not establish
real simultaneous parent/child execution at every cancellation boundary.

The assignment receiver now carries an immutable vector of typed return frames,
stored outermost first and resumed from the end. Frames represent asserting-body
returns, old/labelled-old, integer and Boolean negation, addition,
subtraction, multiplication, equality, inequality and ordered comparisons. Supported
wrapper chains can compose around Asserting while retaining each evaluator entry
and return action. Addition evaluates its left operand first, then transfers an eligible right
operand with the left value and remaining return frames retained. Each transfer
checks the current runtime guards. Other expression families retain
local callbacks. Guarded logging, packaging and extended-exhale cases are unchanged.

Actual one/two-worker jobs check mixed and labelled old/current heap values,
permissions, branching left operands and a captured tail that reports assertion.false.
A CLI regression checks that an inaccessible left operand fails before a right-side
assertion. A real-Z3 regression with record_possible_triggers enabled compares the local
owned receiver with synchronous nested old/labelled-old evaluation. It checks
saved and wrapped triggers, the original old-state flag, current/partial heap
identity, and missing-label failure before receiver entry. Its scheduler and
drained sibling future are injected: it does not inspect a transferred worker
receiver with trigger recording enabled.

The rule-error bridge pass preserves direct Context/Service errors in evaluator,
producer and consumer adapters, including method/function/predicate and guarded
wand paths. Worker regressions inject cancellation and a distinct Diagnostic at
function-precondition and ordinary assertion-tail checkpoints. Reverting either
bridge alone makes its cancellation test fail with a formatted error. The existing
rule unit suite also passes. Execution, method/function/predicate and guarded wand adapters now preserve
typed errors across the reviewed direct context/service boundaries. Conditional
evaluation, production and consumption regressions cover successful cleanup and
an independent cleanup error after callback failure, plus a nested inhale tail.
The injected error occurs after a successful solver pop; these checks establish
error retention, not state recovery after an actual failed pop. This covers the inspected adapters; it does not establish exhaustive coverage
of every nested error family or callback site.

Both-operand tests assert actual submissions and executions on each side with
one and two workers, including an else-only right permission failure. A separate
probe cancels after the right receiver starts and its sibling has been submitted;
it checks typed cancellation and pool draining, without assuming that sibling
has already executed. Both run under an external process watchdog.

Quantified single/general retry continuations preserve their typed callback
errors across both retry layers. Independent negative controls restoring either
old bridge lose the expected Diagnostic. Resource summaries, ordering, removal,
consolidation and mask/wand operations preserve the inspected nested
Service/Solver/Fresh/Render errors. The full real-Z3 library suite passes; these
additional resource mappings have source/type review but no per-site injected
failures. Pure transformation errors retain their existing diagnostic formatting.

The final inspected follow-up preserves solver errors during summary-alias
lookup and service errors during mask trigger adaptation and function body/post
translation. No further reachable loss sites were confirmed in this bounded
review; uninspected code is not claimed to have exhaustive error-path coverage.

Strict operator returns reuse the ordinary evaluator term/debug constructors.
Real one/two-worker checks observe both operand submissions and executions;
source-matched permission failures check left-before-right order and that a
failed right operand skips the captured tail. Division/remainder, short-circuit
and conditional expressions, function/field/collection arguments still
use local callbacks when their exact return action is not represented.

Owned expression descent rechecks transfer eligibility at every subtree entry.
If a borrowed left operand changes the guard, the remaining subtree evaluates
synchronously before resuming the saved return frames and exact assignment
receiver. A real-Z3 test injects that change after Add/Sub left operands; it
checks no submitted job, one correct result, the captured failing tail and an
earlier permission failure that skips assignment and tail.

Asserting bodies now retain their own typed return action, including trigger
recording and outer heap/reserve/exhale restoration. Eligible nested bodies can
transfer; other bodies evaluate locally through the same return action. Actual
one/two-worker checks observe outer and inner jobs, preserve mixed old/current
values and permissions, and reject failures in source order before the caller
tail. A separate inner-receiver test now cancels after an inner sibling is submitted,
checks typed cancellation and drains the pool with one/two workers. It does not
assert that sibling execution began or directly inspect parent solver state;
the cooperative restoration regression covers parent depth/options separately.

Owned descent selects a supported path once using an iterative traversal, then
appends return frames and resumes them in reverse. This removes repeated suffix
searches and front insertion. The evaluator still descends recursively, and
right-operand callbacks and later transfers still clone outer frames; this is
not a general linear-time or stack-safety guarantee.

Let values and bodies now have explicit bind/return frames. They preserve the
ordinary evaluator fresh definition, recorder entry/exit, trigger substitution,
debug reconstruction and returned store binding. Actual one/two-worker tests
cover transfers from both value and body, nested distinct binders, an existing
outer local, old/current heaps and permission failures before the caller tail.
An internal-only test checks an existing identical store key; pinned Silver
rejects duplicate source binder names. Let-specific trigger recording and debug
reconstruction have static source comparison, not independent runtime fixtures.
A LetBody receiver cancellation probe checks typed cancellation and pool draining
after sibling submission, without claiming sibling execution or direct parent
solver-state inspection at that hook.

Inequality uses the same strict return frames and ordinary term/debug constructors.
Actual one/two-worker jobs cover both operands; source-matched permission failures
check left-before-right order and a failed right operand skipping the caller tail.
