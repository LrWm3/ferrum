# Parsed Viper backend performance

The independent audit passed all 240 paired blocks and 480 trials: 480 valid, zero censored, invalid, or missing; postflight reported no errors. Each of four frozen Viper programs was run with both backends, five randomized paired repetitions, workers 1/2/4, branch parallelism off/on, and fresh or reused mode. The reused measurement is one three-request session. Three programs verify; the fourth has the expected failure ID and position. These are parsed Viper measurements, not direct Prusti AST comparisons.

The one-worker, branch-off paired median speedups range from 1.79–5.38× for fresh processes and 1.78–3.04× for three-request sessions. Worker and branch changes do not consistently reduce elapsed time across these cases.

The reference is Silicon `ff386aec4664231dc6f2cb56d8d35f1623088363` with Silver `c4f54b84703a04434b03e97bfea87dbd09870fd2`, Java 17 and the same pinned stdio Z3 4.16 executable. This is separate from the forthcoming direct-Prusti experiment using its bundled JVM backend.

Runs used Ferrum runtime `afdf10cf59106c38d09df32939f1aa9c77d0b989`, Silicon internal caches on, and plain drivers. Rust 1.89 dev profile used opt-level 1 for Ferrum and driver; it is not a release build. The host was an Intel i5-1345U with 12 logical CPUs, Linux x86-64, and all reported CPU governors set to powersave. Wall time includes verifier process startup, parsing, verification and shutdown; previous trials and artifact checks warm the OS file cache. GNU time records decimal seconds, typically at 0.01-second resolution.

## One worker, branch parallelism off

Each cell is median seconds (minimum–maximum), five samples. Paired ratio is the median (minimum–maximum) of the five within-block source/native wall ratios, not a ratio of medians.

| Case | Mode | Native seconds | Source seconds | Paired source/native |
|---|---|---:|---:|---:|
| mut_element_array_pass | fresh | 2.68 (2.07–3.18) | 7.39 (6.84–12.50) | 3.45 (2.15–5.10)× |
| mut_element_array_pass | reused | 7.08 (5.90–8.21) | 14.22 (11.20–19.61) | 1.90 (1.67–3.11)× |
| mut_element_array_wrong | fresh | 2.39 (2.18–3.44) | 7.76 (7.47–12.37) | 3.43 (2.99–4.45)× |
| mut_element_array_wrong | reused | 6.73 (6.03–9.13) | 12.30 (11.75–12.93) | 1.84 (1.38–1.95)× |
| mut_element_option_pass | fresh | 5.83 (4.54–6.06) | 8.78 (8.29–15.23) | 1.79 (1.45–2.51)× |
| mut_element_option_pass | reused | 13.81 (12.94–18.08) | 23.25 (16.17–24.89) | 1.78 (0.89–1.92)× |
| observation_pass | fresh | 1.87 (1.43–2.08) | 8.14 (5.99–11.20) | 5.38 (3.19–5.94)× |
| observation_pass | reused | 5.65 (4.27–6.23) | 17.17 (11.67–18.53) | 3.04 (1.97–4.24)× |

## Worker and branch effects

Each entry is the configuration median divided by the same case, mode and backend’s one-worker/branch-off median. Values below 1 are shorter in this sample; these are ratios of group medians, not paired effects. Each median has five observations.

| Case | Mode | Backend | 1/on | 2/off | 2/on | 4/off | 4/on |
|---|---|---|---:|---:|---:|---:|---:|
| mut_element_array_pass | fresh | native | 1.11× | 0.79× | 0.90× | 1.10× | 0.88× |
| mut_element_array_pass | fresh | source | 1.10× | 1.03× | 0.99× | 1.24× | 1.06× |
| mut_element_array_pass | reused | native | 1.19× | 1.08× | 1.07× | 1.02× | 0.99× |
| mut_element_array_pass | reused | source | 1.41× | 0.90× | 0.82× | 0.87× | 0.84× |
| mut_element_array_wrong | fresh | native | 1.01× | 0.94× | 1.02× | 1.05× | 1.12× |
| mut_element_array_wrong | fresh | source | 0.96× | 1.20× | 1.01× | 0.93× | 0.98× |
| mut_element_array_wrong | reused | native | 1.06× | 1.13× | 1.08× | 1.12× | 1.46× |
| mut_element_array_wrong | reused | source | 0.98× | 1.52× | 1.08× | 1.34× | 1.70× |
| mut_element_option_pass | fresh | native | 0.91× | 1.10× | 0.85× | 0.86× | 1.11× |
| mut_element_option_pass | fresh | source | 0.99× | 1.33× | 0.98× | 1.01× | 1.07× |
| mut_element_option_pass | reused | native | 1.12× | 1.05× | 1.06× | 1.35× | 1.29× |
| mut_element_option_pass | reused | source | 1.05× | 1.02× | 0.68× | 0.87× | 0.70× |
| observation_pass | fresh | native | 0.91× | 1.08× | 1.12× | 1.01× | 0.99× |
| observation_pass | fresh | source | 0.78× | 1.21× | 1.28× | 0.83× | 0.88× |
| observation_pass | reused | native | 1.09× | 1.04× | 0.88× | 1.00× | 1.31× |
| observation_pass | reused | source | 0.97× | 0.63× | 0.62× | 0.93× | 0.96× |

The small sample and observed ranges limit generalization; no aggregate across these distinct workloads is implied. Reused measurements cannot be divided into per-request latencies. The records do not isolate symbolic execution or solver time.

The full audited metrics, all within-pair values, configuration counts, fixture and tool hashes, and host metadata are in `performance-backend.json` (SHA-256 `5f6165bcdcc87cff0aa15ea98a2a3f1b2111328c1f0c8c4ddf8f6528ec352622`). The raw run manifest, schedule, summary and JSONL trial stream are hash-linked there; raw session and timer hashes are checked by the independent audit at `/tmp/ferrum-stage5-analysis/backend-report.json` (SHA-256 `3f321129b83f442cef8809e5321ef52ba2eb0d25466919550f2af82d7da12678`). The run artifacts remain under `/tmp/ferrum-stage5-backend-results`. Readiness gates are documented in [performance-validation.md](performance-validation.md). The companion JSON also preserves all trial rows and their verification records; complete raw session transcripts remain in the hash-linked run directory.
