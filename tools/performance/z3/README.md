# Experimental solver CPU accounting

These Linux tools wrap stdio Z3 and collect process CPU via `wait4`. Both backends
forcibly stop solver processes, so a wrapper alone can disappear before writing
its final accounting record. The wrapper records the real child's PID and start
ticks before allowing exec; the outer subreaper can then match the adopted child's
`wait4` record when the wrapper is killed. The assessor accepts exactly one
matching wrapper or adopted record, never both. Missing or conflicting records
are incomplete.

Build in an isolated copy of this directory, then run the fake checks:

```sh
cc -std=c11 -O2 -Wall -Wextra -Werror z3-wait4-wrapper.c -o z3-wait4-wrapper
python3 test_v2.py
```

Set `FERRUM_Z3_REAL` to the frozen actual Z3 executable and
`FERRUM_Z3_RECORD_DIR` to a new directory. Supply the wrapper as the verifier's
Z3 executable, launch through this directory's `run_session.py`, and pass the
accounting directory and session JSON to `assess.py`. Preserve hashes for all
tools, identities and raw results. The wrapper must not replace the real solver
for primary uninstrumented timing.

The initial real controls passed exact native/source normal
pass/failure/pass/parse-failure/pass behavior and native timeout-to-valid recovery.
All 14 observed real solver identities were accounted for, with clean process
reaping. The frozen artifact hashes, full comparisons and accounting records are
in [the control evidence](../../../porting/performance-accounting-controls.json).
Those short controls validate behavior; their durations are not benchmarks.
They do not prove overhead is negligible on larger workloads.

GNU time accounts for the foreground process tree it reaps. Adopted children are
reaped by the outer supervisor, so instrumented total CPU must add their disjoint
`wait4` CPU to the foreground timer. Solver CPU is the sum of identified solver
records. The remaining CPU includes frontend, language runtime, wrapper and other
work; it is not exclusive symbolic execution. Solver process CPU includes
startup, SMT parsing, solving and cleanup, not just `check-sat`. Never subtract
overlapping elapsed wall times. Missing identities or timers are unavailable,
never zero. PID tracking covers observed descendants and cannot prove that every
rapidly escaping process was discovered. GNU time's usual 0.01 s rounding also
limits small residuals.
