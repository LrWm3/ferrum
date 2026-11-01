# Z3 SMT-thread screen on the frozen nested iterator

Keep `smt.threads=1` for this workload. All three single-thread runs verified;
all six runs using two or four SMT threads reached the 60-second verification
limit. The nine-run batch completed in seven minutes on November 1, 2026.
This is a bounded result for one frozen Rust fixture, not a universal result
about Z3 parallelism or a new Ferrum-versus-Silicon comparison.

| Z3 SMT threads | Verified | Request seconds, in block order | Median successful request |
| --- | ---: | --- | ---: |
| 1 | 3/3 | 8.51, 11.14, 11.37 | 11.14 s |
| 2 | 0/3 | 65.07, 62.59, 62.55 (all verifier timeouts) | Unavailable |
| 4 | 0/3 | 61.72, 61.48, 62.25 (all verifier timeouts) | Unavailable |

Timeout observations are censored: their request times include client overhead
and cancellation, and are not completed proof times. The backend phase of the
single-thread runs took 6.845, 9.048 and 8.625 seconds. The multithreaded runs
reported cancellation while verifying `m_visit`. This screen establishes the
regression but does not locate the expensive SMT query or explain its cause.

The case is the preserved `mut_element_nested_pass` from Prusti source
`a59ed917c1c3c4c4ca6ff1de12ad20d48491d021`, with PCG
`c18a51899e37e0fa67f9b5f17f7d518ef2f5518c`. It is the historical input used for
the [snapshot-trigger investigation](performance-summary-triggers.md), rather
than the subsequently edited fixture with the same name on the live branch.
The native server is the preserved `trigger-server` from the
[trigger refinement](snapshot-trigger-refinement.md); its SHA-256 is
`e94e0f5763e3feb906ed8c9ffeec10842453dcb2210fdfe523d365087949243f`.
It is not a rebuild of current Ferrum HEAD. The JSON records the source,
client, server, solver and runner identities.

Only Z3's `smt.threads` setting varied. Controls were Z3 4.16.0, one Ferrum
worker, branch parallelism off, snapshot-summary triggers on, internal caches
on and Prusti's result cache off. Existing solver options, resource limits
and saturation policy were retained. `parallel.enable` and `sat.threads`
were not changed. The verifier options were:

```text
--timeout=60 --numberOfParallelVerifiers 1 --parallelizeBranches=false --snapshotSummaryOnlyTriggers=true
```

Each trial used a fresh server and a disposable copy of the same dependency
seed, with only the root Rust fixture checked. Request timing includes the
Rust client, encoding and backend verification, and excludes server launch,
seed copying and cleaning. Limits were 60 seconds for verification, 100 seconds
for the client and 1,200 seconds for the batch. Every scheduled observation is
retained, with no performance retries. The serial order rotated across blocks:
`1,2,4`; `2,4,1`; `4,1,2`.

All servers and their solvers had the same affinity to CPUs 4–7, four distinct
efficiency cores on an Intel Core i5-1345U. Other Prusti work continued on the
shared host. Older profiles used CPUs 0–3, so their absolute request times
should not be compared directly with these. The repetitions support keeping
one SMT thread on this case; they do not establish a small percentage effect
or justify a claim about the complete stdlib matrix.

A wrapper added `smt.threads=N` to the Z3 command line, with stdin/stdout
inherited directly and no SMT relay. Before timing, `(get-option :smt.threads)`
returned exactly 1, 2 and 4 for the three configurations. Each real solver's
initial metadata records the requested command and affinity. An independent
live `/proc` observation during `block2-threads4` recorded a Z3 process with
five OS threads and affinity 4–7, confirming that additional threads ran.

There are two measurement limitations in the original harness records:

- The older result classifier missed the lowercase diagnostic
  `verification timed out after 60 seconds`, labelling those six observations
  `unexpected_result`. The derived JSON records them as `verifier_timeout`
  using both that client diagnostic and the server cancellation message.
  The original records are preserved. Their `timed_out=false` field refers
  to the outer client watchdog, which did not expire.
- The wrapper's final CPU/RSS records were not flushed during solver shutdown.
  Its initial zero counters, and the batch's resulting zero resource totals,
  are missing measurements. Derived CPU and peak-RSS values are explicitly
  null. The single live RSS observation is not a peak or a comparison.

Preflight and postflight checks matched all 4,254 frozen artifact hashes and
the dependency seed tree hash. All nine dependency checks, request timers and
client/service cleanup audits passed. The batch supervisor also exited cleanly
with no owned descendants pending cleanup. A Python syntax error in the initial
batch setup was corrected before preflight or any timed trial; that setup
failure is retained separately and is not a performance observation.

[Derived evidence](performance-z3-threads.json) includes per-run classifications,
phase times, controls and artifact hashes. The
[raw archive](evidence/z3-threads/observations.tar.gz) preserves the runners,
manifest, all nine client/server logs and result records, option controls,
cleanup audits and batch supervision. Original artifacts are also at
`/tmp/ferrum-z3-threads-20261101`. The archived scripts depend on the frozen
inputs and helper paths recorded in the manifest; they are historical experiment
scripts rather than a portable benchmark installation.
