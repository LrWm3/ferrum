# Comparable saturation experiment protocol

The user requested testing saturation settings on the actual Prusti-generated
workloads after the code review identified differences between bundled Silicon
and the newer upstream defaults ported by Ferrum. This protocol was frozen
before the first measurement. Runtime code and global defaults are unchanged.

## Explicit profiles

All profiles use a 100 ms saturation base. The weight order is preamble,
contract, unfold, inhale, repetition.

| Profile | Explicit weights | Purpose |
| --- | --- | --- |
| `modern` | `[1,0.5,0.4,0,0]` | Newer upstream/native defaults |
| `repeat_only` | `[1,0.5,0.4,0,0.02]` | Toggle repetition alone relative to modern |
| `legacy` | `[1,0.5,0.4,0.2,0.02]` | Full older bundled defaults |
| `common_off` | `[1,0,0.4,0,0]` | Suppress both moved contract/inhale slots; repetition off |
| `common_on` | `[1,0,0.4,0,0.02]` | Same altered policy with repetition on |

Both backends receive every selected vector explicitly. The older source uses
the contract slot at some loop/callee/branch sites where newer source and Ferrum
use inhale. Equal vectors alone therefore do not establish equal calls/budgets.
The common controls deliberately disable both slots, including genuine
precondition saturation; they are altered policies, not either version's defaults.
Their purpose is a cleaner repetition comparison. Actual prover comments and
wire options remain necessary evidence of effective behavior.

## Cases and fixed schedule

- `mut_element_nested_pass`: all five profiles, both backends, three repetitions
  per profile/backend: 30 successful-verification observations planned.
- `mut_element_array_pass`: modern, repeat-only and legacy, both backends,
  three repetitions: 18 successful-verification observations planned.
- `mut_element_array_wrong`: all five profiles and both backends once: ten
  readiness controls requiring `exhale.failed:assertion.false` at
  `mut_element_array_wrong.vpr@1786.10--1786.82`. These do not enter positive
  performance aggregates.

Total: **58 captures**, including 48 repeated positive trials and ten controls.
Within each case/repetition block, profile/backend order is randomized with seed
20261030. Main block order is randomized; controls precede every main trial.
The complete schedule is written before execution. A failed readiness control
stops the primary run and retains the failed evidence. Main-trial failures and
timeouts are retained, with no favorable-result retries or zero-valued timings.
Ratios use complete valid matched repetition indices only, with excluded samples
and variability reported. There are at most three independent values per cell.

## Fixed artifacts and settings

Native is the existing afdf10c dev-profile plain backend driver; source is the
existing plain Java driver compiled against the actual Prusti bundled Silicon
6b540aa4 jar. Input bytes are the committed generated Viper fixtures. All drivers,
classes, jar, Z3, scripts and inputs have before/after hashes in the frozen spec.
The initial spec and schedule were prepared under
`/tmp/ferrum-saturation-experiment`. Its readiness gate stopped after six
controls: all expected proof outcomes were met, but one source-owner trace lost
the final command because the relay forwarded it before recording it. No primary
positive trial started. That failed attempt remains under
`/tmp/ferrum-saturation-results` and is excluded from the new matrix.

The V2 relay persists both directions before forwarding, with real byte-equality,
protocol and 20 immediate-kill-after-acknowledgment controls passing. The revised
frozen spec/schedule is under `/tmp/ferrum-saturation-experiment-v2`, with new
output `/tmp/ferrum-saturation-results-v2`. Inputs, profiles, seed, schedule and
all verifier settings are unchanged. Earlier relay/tools remain immutable.

Both use the same Z3 4.16 executable, one worker, branch parallelism off, internal
caches on, 180-second program and 300-second outer limits, one error, complete
exhale, termination plugin disabled, assertion setting 10000 and Prusti options
`smt.qi.eager_threshold=1000 model.partial=false smt.arith.solver=6`. The source
Boolean branch flag is omitted to retain its checked false default; native uses
explicit false. Resource-bound mode remains active; saturation milliseconds are
converted into Z3 resource budgets rather than fixed wall-clock durations.

All timed driver descendants and offline solver replays are restricted to
logical CPUs 0–3, the host's two physical performance cores. This avoids switching
between performance and efficiency cores. It is not exclusive reservation or
fixed frequency. Governors remain powersave and ordinary background processes
remain running. No other verification run was active at preparation. Runs are
serial; host/load snapshots are recorded. These conditions differ from earlier
measurements, so their timings are not pooled.

## Capture, solver replay and audit

Every trial uses the checked transparent Z3 relay and prover logs. Session
supervision retains proof outcomes, error IDs/spans, exceptions and process
cleanup. Command/response alignment, chunk completeness, query counts, response
kinds and saturation comment categories are audited per solver. The final
per-process metadata may lack an exit field when the verifier terminates its
relay; cleanup and captured-stream completeness are separate checks.

After each capture, replay each exact fixed stdin stream through a fresh identical
Z3 on the same CPU set, appending `(get-info :all-statistics)`. The full original
response prefix must match before its statistics enter aggregates. The replay
has a 180-second outer bound. Capture wall time, observed check-response waits,
offline CPU/wall and reported work counters are separate measurements. Source's
two solver-process counters/CPU are summed only within that trial; overlapping
waits are not an exclusive application decomposition. Offline replay follows a
fixed captured path rather than rerunning verifier decisions.

Full legacy versus modern and repetition-only versus modern are within-backend
effects. Common-on versus common-off further isolates repetition with both moved
slots disabled. Cross-backend observations retain all other known context/order
differences. A result on these two cases does not choose a global stdlib default;
larger coverage would be needed before promoting a setting change.

The runner is [run_saturation.py](../tools/performance/smt/run_saturation.py).
Schedule/outcome rejection checks and real Z3 relay controls pass before the run.
All evidence and independent post-run analysis must be reviewed before reporting
any conclusion.
