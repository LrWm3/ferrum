# Direct Prusti profile and path-condition copying

Ferrum `4cda819` removes redundant copies when maintaining path conditions.
On the nested mutable-iterator case, the native verification worker used about
**10.2% fewer sampled instructions**, while Z3's instruction count differed by
less than 0.01%. This is evidence of less native work, **not an established
end-to-end latency improvement**: the short paired timing runs were noisy.

Z3 remains the dominant cost. In the initial direct-Prusti CPU profile it
accounted for 958 of 1,129 samples, or **84.9%**. Quantifier matching was prominent
in its recovered stacks. Removing a fraction of the remaining native work
cannot eliminate that solver cost.

## What was measured

Unlike the earlier parsed-`.vpr` profiles, these runs invoke `cargo-prusti` on
the actual Rust fixture `mut_element_nested_pass`. The client sends VIR to a
fresh native Prusti server, which converts it directly to a Silver AST. The
parsed-Viper frontend is bypassed, although builtin preamble processing can
still use parser code.

The client, adapter and fixtures are frozen at Prusti
`a59ed917c1c3c4c4ca6ff1de12ad20d48491d021`, with PCG `c18a5189`.
Only the server's Ferrum dependency changes: baseline `49d3737` versus candidate
`4cda819`. This is **not** a new verification matrix on the latest stdlib branch.
The active stdlib checkout was not edited. Source and build caches were copied
to `/tmp/ferrum-direct-profile-49d3737`; preserved baseline and candidate server
binaries have separate hashes in the evidence.

Both binaries use the same development profile, with the three Ferrum packages
at optimization level 1, and `nightly-2026-08-15`. Configuration is one worker,
branch parallelism off, outer result cache off, internal caches on, and the
existing saturation/solver defaults. There is no separate method solver here.
Server and solver affinity is CPUs `0,1,2,3`. Verification/client limits are
60/100 seconds. Every run starts a fresh service and checks only the root Rust
fixture package from a disposable dependency seed.

The initial profile verified successfully: Rust-to-VIR encoding took 0.262 s,
VIR conversion 0.035 s, backend verification 11.480 s, and the client request
12.55 s. The request interval excludes service startup. These phase times do
not sum to the whole request: compilation, communication, consistency checking
and cleanup also contribute.

## Change and correctness

The port's ordered set used a full `IndexSet` clone for functional `incl` and
`excl`. Path-condition updates repeatedly assigned those cloned results back to
an already exclusively borrowed set. Growing the accumulated assumptions thus
copied all existing entries on every insertion. Reading branch conditions also
created a recorded snapshot of entire assumption layers just to select their
branch terms.

The change adds crate-private owned set updates and uses them in the mutable
path stack. Removal still preserves order through `shift_remove`; this is not
a claim of constant-time removal. The public functional set API and explicit
snapshot clones retain their original value semantics. A direct branch-term
projection replaces five unnecessary full-stack snapshots.

New regressions check zero element copies during owned updates, insertion and
reinsertion order, set equality, and isolation of recorded/forked paths after
the live stack changes. Existing duplicate-assumption scope behavior is
preserved. All **303 enabled Silicon unit tests passed** (43 opt-in tests
ignored), and the workspace/all-targets check with `native-z3` passed.

Actual Prusti captures, with the audited byte relay, preserve **complete,
byte-identical SMT input and output**:

| Rust fixture | Outcome on both versions | Solver checks | Input bytes |
| --- | --- | ---: | ---: |
| `mut_element_nested_pass` | Verified | 1,111 | 4,413,684 |
| `mut_element_array_wrong` | Expected assertion failure at Rust line 8 | 475 | 1,020,006 |

Both transcripts have no protocol gaps. A bounded offline replay of the nested
baseline reproduces every response and reports 181,264 quantifier
instantiations and 18,540,052 resource units. The candidate sends the same
bytes, including resource limits and query order. The smaller positive
`mut_element_array_pass` also verifies in all four timing runs. No trial timed
out; client and service cleanup audits found no remaining owned descendants.

## Instruction evidence

The CPU profile used user CPU-clock samples at 99 Hz and 65,528-byte DWARF
stacks. Rust worker call chains failed to unwind in this build; their sampled
instruction pointers still identify allocation, AST traversal/equality and
collection cloning. Z3 stacks were recovered. The code review confirmed the
unnecessary path-set and layer copies; the profile does not precisely attribute
all allocation time to them.

Because clock-based timings varied, a separate short profile of each binary
sampled every 1,000,000 retired user instructions. Both used the same core PMU
(`cpu_core/instructions/u`), with inherited worker and solver events. Neither
reported lost samples. Figures below are sample counts, not exact instruction
totals; partial periods at thread boundaries are omitted.

| Process/thread | Baseline samples | Candidate samples | Change |
| --- | ---: | ---: | ---: |
| Server / adapter | 1,174 | 1,174 | 0.0% |
| Native verification worker | 12,663 | 11,376 | **−10.2%** |
| Z3 | 48,475 | 48,479 | +0.008% |
| Entire sampled server tree | 62,312 | 61,029 | −2.1% |

Including the server/adapter samples, native instructions fall about 9.3%. The almost
unchanged solver count is a useful control: the instruction reduction is in
Ferrum rather than a different solver search. This remains one instruction
profile per binary on one case, not a general stdlib performance result.

## Paired latency measurements

Uninstrumented trials used baseline/candidate/candidate/baseline order for each
positive fixture. The last pair is displayed below as baseline versus candidate.
All observations are retained; none were retried or excluded. Backend time
includes solver work. Native CPU is the server process's user plus system time;
solver CPU is its reaped child CPU time, captured separately with `/proc`.

| Fixture / pair | Baseline backend s | Candidate backend s | Baseline request s | Candidate request s |
| --- | ---: | ---: | ---: | ---: |
| Nested / 1 | 15.417 | 20.042 | 16.57 | 21.72 |
| Nested / 2 | 18.358 | 18.448 | 19.62 | 19.98 |
| Array / 1 | 0.746 | 0.735 | 1.41 | 1.52 |
| Array / 2 | 0.756 | 0.699 | 1.40 | 1.42 |

Nested solver CPU alone changed from 13.13 to 17.39 seconds in the first pair,
despite unchanged solver input. The second pair was closer: 15.74 versus 15.97
seconds. Native CPU moved from 2.57 to 3.10 seconds and from 2.96 to 2.80 seconds,
respectively. Small array backend reductions do not translate to improved whole
request times in these observations. There is no reliable latency win to claim
from these pairs on the shared host.

The eight timing runs, two negative captures and candidate CPU profile completed
in 112.9 seconds. Initial preparation/builds, initial profiles/captures and the
two follow-up instruction profiles are outside that interval.

## Evidence and reproduction

[Machine-readable evidence](performance-path-conditions.json) retains results,
pair order, hashes, solver transcript audits, replay statistics, CPU and
instruction samples, environment overrides, cleanup audits and check summaries.
Raw evidence is at `/tmp/ferrum-direct-profile-49d3737`. The three retained
`run_direct_v*.py` harness versions separate the initial profile/captures, added
process CPU accounting, and added instruction sampling. The original version's
hash matches the preparation manifest.

The isolated native server build command was:

```sh
cargo +nightly-2026-08-15 build --locked --offline \
  -p prusti-server --no-default-features --features ferrum \
  --bin prusti-server-driver
```

The initial build first updated the isolated lockfile for local Ferrum path
dependencies. The candidate build used `--locked`. Source paths, target paths
and required environment are recorded with the raw preparation/build logs.
`compare.py` drives the bounded ABBA block; `run_direct_v2.py --instructions`
adds hardware sampling to one fresh request.
