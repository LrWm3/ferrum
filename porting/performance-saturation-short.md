# Short saturation check after deterministic emission

Four fresh Ferrum captures and their solver-only replays completed in **158.7
seconds**. On the nested iterator workload, the full older weights consistently
reduced solver work, but elapsed times did not establish an overall speedup.

The existing development binary includes both ordering fixes at runtime
`4bef39a`. The predeclared order was current, older, older, current: two pairs
with reversed order. Only `mut_element_nested_pass` was tested, with one worker,
branches off, internal caches on and the same Z3 4.16 binary and input bytes as
the earlier experiments. No rebuild or expanded matrix was required.

The saturation base was 100 ms. Current weights were `[1,0.5,0.4,0,0]`; older
weights were `[1,0.5,0.4,0.2,0.02]`, in preamble/contract/unfold/inhale/repetition
order. This compares two complete settings on the same Ferrum runtime; it does
not isolate the inhale and repetition slots individually or compare Silicon.
To bound the short check, program/outer/offline limits were 60/75/45 seconds;
the per-query resource limits and solver options were unchanged.

| Metric | Current weights, two observations | Older weights, two observations |
| --- | ---: | ---: |
| Capture elapsed time | 28.63 s, 29.17 s | 25.03 s, 37.08 s |
| Offline Z3 CPU | 10.02 s, 12.12 s | 6.66 s, 5.84 s |
| Quantifier instantiations | 181,264 each | 95,396 each |
| Z3 resource counter | 18,540,052 each | 10,823,650 each |
| Solver checks | 1,111 each | 1,214 each |

Older/current paired elapsed ratios were **0.874** and **1.271**: one pair was
12.6% faster and the other 27.1% slower. Older weights reduced quantifier
instantiations by **47.4%**, resource work by **41.6%**, and offline solver CPU
by 33.5% and 51.8% in the two pairs. The 103 extra checks consist of 69
after-inhale and 34 before-iteration saturations. The combination reduces later
solver work enough to lower the aggregate counters despite adding checks.

Both observations of each profile have byte-identical SMT inputs and responses,
and identical work counters. All four captures verified, passed protocol and
cleanup checks, and reproduced every original response in their fixed-stream
replay. Effective SMT options/resource budgets and artifact hashes were checked.
There were no retries, censored observations or failed captures.

This is a small tuning screen on one parsed-Viper workload. Capture elapsed time
includes frontend/startup/relay/shutdown costs on a shared host; offline solver
CPU is measured separately and cannot be subtracted to derive exclusive phase
times. Two pairs do not establish a latency improvement or justify a global
default change. This run adds no negative control or broad correctness matrix.
No runtime code or default changed.

The [machine report](performance-saturation-short.json) contains the frozen spec,
schedule, full trial records, paired ratios, validation results, runner source
and evidence hashes. Raw captures and replays remain under
`/tmp/ferrum-saturation-short-4bef39a`. The earlier
[larger sweep](performance-saturation.md) predates deterministic emission and
remains a separate experiment.
