# Native continuation ownership

The current method, statement, CFG edge and loop frames own their captured
data. Their outer continuations still execute through borrowed callbacks.
This is sufficient for synchronous execution, but does not make an arbitrary
branch transferable to another verifier thread.

The source references are Silicon's pinned [Executor.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Executor.scala),
[ExecutionFlowController.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/ExecutionFlowController.scala)
and [MethodSupporter.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/MethodSupporter.scala).

The internally gated joined CFG and predicate jobs have a finite boundary:
workers return owned join entries and declarations while the calling verifier
retains its continuation and cleanup obligations. Evaluator joins that explicitly
disable branch parallelism upstream remain synchronous.

Nonjoined offloading must also carry the work that follows a branch:

- Statement completion restores reserve heaps and closes the statement record.
- Remaining statements, block completion and edge folds preserve source result
  combination, short-circuiting and path allocation order.
- Loop entry produces and consumes invariants in separate local solver scopes.
  Each recorded phase replays paths and declarations before executing its body.
- Local and branch scopes must unwind on both verification and service errors.
- Producer, consumer and evaluator continuations can invoke their caller more
  than once; retry and logging boundaries must survive that behavior.
- Method completion prepares and consumes postconditions after CFG execution.

A transferable continuation representation must encode these operations through
the method terminal, including pending cleanup, errors, warnings and cancellation.
Solvers remain on their owning threads; jobs may carry immutable replay snapshots
and symbolic state, but cannot carry a live verifier or borrowed solver scope.
Moving another group of captured fields into a struct does not satisfy this
requirement. Public branch scheduling remains gated until that executable chain
and its restoration behavior are complete.
