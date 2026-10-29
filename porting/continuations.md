# Native continuation ownership

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
Cancellation tests cover an in-flight terminal job and cancellation of the then
action after else submission, retaining typed cancellation and restoring parent
solver depth and options before return.

## Remaining scope

The public parallel-branch option remains gated. Loop successor propagation now
carries the terminal through replayed loop-body and exit paths. Invariant
collection stays local, and backedges stop at invariant re-establishment. Actual
Z3 checks separately exercise forks in the body and after the exit edge with one
and two workers. The same-worker isolation fix is shared by terminal, joined and
evaluation jobs; a regression prevents an outer branch from falsely proving an
assertion using the suspended inner branch's assumptions.

Additional producer/consumer callers, snapshot-returning consumption, predicate
contents, active logger scope migration and general borrowed callback entry
points still need owned caller frames. Conditional/implication rules and nested lets, statement sequences, TryBlock
and loop-head statements have executable owned caller frames. Loop invariant
collection/establishment and additional method/predicate callers remain pending. They retain synchronous execution. Joined CFG/predicate dispatch
also falls back synchronously when member logging, packaging or extended exhale
is active. Broad parallel compatibility remains incomplete. Conditional scope
closures may be bypassed only when the native context proves them to be no-ops;
active member logging disables this owned terminal dispatch.

Packaging proof scripts and joined consumer branches explicitly disable branch
parallelism upstream (MagicWandSupporter.scala and Consumer.scala). Their local
execution is source behavior; the outer statement continuation must still resume
correctly afterward.

Moving captured fields into a struct alone is insufficient. New dispatch points
must identify the exact executable continuation, preserve source result order,
and demonstrate restoration on success, verification failure, service error and
cancellation before removing their guard.
