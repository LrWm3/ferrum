# Annotated prover logs for the code review

These gzip files preserve the native and source-worker prover logs used to
locate high-level saturation comments and the aligned permission-removal check.
The [code-review machine record](../../performance-code-review.json) binds their
compressed and uncompressed bytes, original paths, lengths and saturation-comment
line numbers. Gzip timestamps are zero.

The source log has 34 `State saturation: before repetition` comments; the native
log has none. These logs include verifier comments and response annotations.
The original [wire captures](../nested-smt/README.md) remain the authoritative
command/response byte streams for solver replay. The [review](../../performance-code-review.md)
distinguishes observed code/trace differences from untested causal hypotheses.
