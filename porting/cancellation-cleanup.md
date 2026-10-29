# Cancellation cleanup diagnostic follow-up

Fresh Prusti verification exposed native commands that exceeded the outer
300-second bound without returning a verifier diagnostic. An observed repeat of
`iterator/mut_native_resource_into_iter_pass` reached Ferrum's deadline monitor;
after Z3 exited, the verification thread continued consuming CPU and its sampled
resident memory grew from about 0.85 GB to 4.25 GB before the harness stopped it.
That observation alone did not identify the executing code.

A controlled AST integration probe using the original driver and a shorter
60-second verifier limit captured the CPU-active thread after Z3 exited. Its
stack ran through `str::Debug`, `String::fmt`, `NativeError::fmt`, executor error
formatting and `finish_native_predicate_operation` at the callback-cleanup macro.
The debugger passed SIGPIPE through to preserve ordinary failed-write handling.
This is evidence from an instrumented cancellation probe, not a proof outcome or
an original-budget performance comparison. Separate parsed-text and AST debugger
runs finished normally before a stack capture; their results do not replace the
original matrix or establish deterministic reproduction.

## Cause and correction

Native cleanup scopes retain both an original error and a failed cleanup. Some
adapters store their rendered diagnostics in `NativeError` string variants.
Derived Rust `Debug` then quotes and escapes those strings again when a parent
scope formats its error. Repeated scopes multiply the existing backslashes and
can make diagnostic text grow exponentially while unwinding a killed solver.

`NativeError` now renders its existing string payloads verbatim. Typed variants
retain their normal structural formatting, and constructors and payload types
remain the same. This preserves the original error text and cleanup details
without repeatedly escaping them. It intentionally changes Rust `Debug`
presentation for these internal error strings. It does not impose a general
memory bound or deduplicate genuinely separate branch error trees.

## Validation

The regression uses twelve actual `NativeVerifierContext::locally_loop` scopes
and an owned fake stdio solver. It kills the child at the innermost operation,
then exercises every failed solver pop during unwinding. The result remains an
error, the primary text containing a quote and backslash occurs exactly once,
all twelve EOF/BrokenPipe cleanup errors remain, and the child is reaped.

The same regression with the original derived `Debug` fails its size assertion
at **58,605 bytes**; the corrected implementation produces **1,295 bytes**. The
regression is deliberately shallow enough to demonstrate the old failure without
an out-of-memory test. Its name is
`nested_interrupted_scope_failures_keep_evidence_without_escape_explosion`.

The checked source file SHA-256 is
`5f11696dda67fae91ec46d7b13e231b5161205a4394174737d8c7560819d81d2`.
Validation over the `c9706b0` parent passed:

- Silicon library: 293 regular tests, followed by all 43 ignored tests with
  real Z3 explicitly enabled.
- Root library: nine regular tests, followed by all twelve ignored tests with
  real Z3 explicitly enabled.
- Linked production build and 23 tests selected by `linked`, including ignored
  tests and controller interruption/worker joining, against Z3 4.16.

These library tests use test-only zero-optimization overrides for the three
Ferrum crates. The production build uses the existing development profiles.
The unchanged Silver library was not rerun for this diagnostic-rendering change;
the earlier 826-test workspace result remains evidence for its recorded revision.

Raw validation logs use the `/tmp/ferrum-stage3-cancellation-` prefix. The old
regression log is `/tmp/ferrum-stage3-cancel-baseline-test.log`. The controlled
AST stack is retained in
`/tmp/ferrum-prusti-stage3/stall-probe/ast-gdb-timeout60-passsig/gdb.log`, SHA-256
`220da7de557fc75b673e454a3b7286d484eb00cc5c95a602078184401a0bc66d`;
its `capture.json` records observed solver exit and active owner CPU.

Prusti rebuilds and affected-fixture reruns are pending. This regression and
stack identify the cleanup defect; they do not by themselves establish that all
original matrix watchdog cases are resolved.
