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

## Remaining scope

The public parallel-branch option remains gated. Loop successor propagation is
under review; the same-worker isolation fix is shared by terminal, joined and
evaluation jobs. A deterministic regression also checks that an outer branch
cannot falsely prove an assertion from the suspended inner branch's assumptions. Active logger scope migration, general borrowed callback
entry points and broad parallel compatibility are not complete. Conditional scope
closures may be bypassed only when the native context proves them to be no-ops;
active member logging disables this owned terminal dispatch.

Moving captured fields into a struct alone is insufficient. New dispatch points
must identify the exact executable continuation, preserve source result order,
and demonstrate restoration on success, verification failure, service error and
cancellation before removing their guard.
