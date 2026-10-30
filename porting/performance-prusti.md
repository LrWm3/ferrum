# Direct Prusti performance measurements

This is a direct-Prusti dev-profile experiment on four actual stdlib workloads, with three randomized paired blocks per case, worker/branch configuration and mode. Prusti uses nightly-2026-08-15 with debug=1 and default opt-level 0; the three Ferrum crates use opt-level 1. It is not a release-build comparison. The native backend is Ferrum afdf10c and the JVM backend is the separately bundled Silicon 6b540aa4 (bundle SHA-256 `6d11d2b73efe97b97026050f13d966c5ec599cf70d43022346382e065a49cf7c`), not standalone reference Silicon ff386. The outer Prusti result cache was disabled; Silicon internal caches used their production defaults.

The audit accounted for 576 requests and 144 service blocks. Effective classifications: `{'valid': 576}`. Each comparison uses validated same-byte calibration dumps, expected Rust outcomes and diagnostics, and no timed dependency rebuild. All 144 expected-negative requests reported the assertion failure at `mut_element_array_wrong.rs:8`; the full request coverage and any exclusions remain visible in JSON. The runner and analyzer retain failed or censored observations; ratios use complete valid pairs only. Full command, source/artifact hashes, raw structured trial references, service audits, schedule and exclusions are in [performance-prusti.json](performance-prusti.json).

The baseline table uses one worker with branch parallelism off. The host is the same Intel i5-1345U with 12 logical CPUs, approximately 32 GB RAM and the recorded powersave governor setting. The primary wall time is GNU time around each client command, typically 0.01 s resolution. Values below show median [minimum, maximum] and sample count. Fresh process includes startup; service first and later requests use a newly started persistent service per block. The two later requests are averaged **within each block**, giving at most three independent block values. JVM/native ratio cells are medians of individual ratios paired within the predeclared pair index, not ratios of the displayed group medians.

| Case | Mode | Native wall s | JVM wall s | JVM/native |
| --- | --- | ---: | ---: | ---: |
| observation_pass | fresh | 1.880 [1.810, 1.910] (n=3) | 6.760 [6.390, 8.230] (n=3) | 3.539 [3.399, 4.547] (n=3) |
| observation_pass | service_first | 1.930 [1.890, 2.220] (n=3) | 11.460 [9.810, 12.130] (n=3) | 5.190 [5.162, 6.285] (n=3) |
| observation_pass | service_later_mean | 1.820 [1.695, 2.230] (n=3) | 3.385 [2.845, 4.270] (n=3) | 1.860 [1.678, 1.915] (n=3) |
| mut_element_array_pass | fresh | 2.510 [1.940, 2.740] (n=3) | 12.660 [7.540, 13.170] (n=3) | 4.620 [3.887, 5.247] (n=3) |
| mut_element_array_pass | service_first | 2.040 [1.920, 2.130] (n=3) | 12.730 [7.840, 13.300] (n=3) | 6.520 [3.681, 6.630] (n=3) |
| mut_element_array_pass | service_later_mean | 1.855 [1.770, 2.435] (n=3) | 4.700 [3.340, 5.595] (n=3) | 2.534 [1.372, 3.161] (n=3) |
| mut_element_option_pass | fresh | 3.390 [3.250, 3.710] (n=3) | 9.840 [9.370, 15.920] (n=3) | 2.903 [2.883, 4.291] (n=3) |
| mut_element_option_pass | service_first | 5.060 [4.500, 5.470] (n=3) | 10.760 [9.510, 14.330] (n=3) | 2.126 [2.113, 2.620] (n=3) |
| mut_element_option_pass | service_later_mean | 3.995 [3.500, 4.110] (n=3) | 6.235 [4.815, 6.830] (n=3) | 1.517 [1.205, 1.951] (n=3) |
| mut_element_array_wrong | fresh | 2.140 [2.060, 2.410] (n=3) | 11.820 [7.490, 12.170] (n=3) | 5.050 [3.636, 5.523] (n=3) |
| mut_element_array_wrong | service_first | 2.240 [2.240, 2.480] (n=3) | 8.580 [7.760, 13.280] (n=3) | 3.830 [3.129, 5.929] (n=3) |
| mut_element_array_wrong | service_later_mean | 2.710 [2.095, 2.720] (n=3) | 4.505 [3.760, 4.765] (n=3) | 1.656 [1.387, 2.274] (n=3) |

For the one-worker, branch-off setting, the median paired JVM/native client-wall ratios range from 2.903 to 5.050 for fresh requests, 2.126 to 6.520 for first service requests, and 1.517 to 2.534 for later-request block means across these four cases. Each cell's count is shown above; the ranges in the table show variability and these figures apply only to the recorded configurations and host.

The following one-worker, branch-off phase values are inclusive median seconds [range]. Native and JVM conversion and backend-verification scopes are not identical; native frontend construction/consistency lies outside its verification span, while JVM verification includes wrapper/polling. They must not be interpreted as an exclusive frontend, symbolic-execution or Z3 split.

| Case | Mode | Backend | Rust→VIR s | VIR conversion s | Backend verification s |
| --- | --- | --- | ---: | ---: | ---: |
| observation_pass | fresh | native | 0.306 [0.254, 0.334] (n=3) | 0.007 [0.006, 0.007] (n=3) | 0.722 [0.654, 0.734] (n=3) |
| observation_pass | fresh | jvm | 0.282 [0.278, 0.292] (n=3) | 0.379 [0.353, 0.453] (n=3) | 4.694 [4.664, 6.174] (n=3) |
| observation_pass | service_first | native | 0.286 [0.267, 0.320] (n=3) | 0.007 [0.006, 0.008] (n=3) | 0.676 [0.598, 0.790] (n=3) |
| observation_pass | service_first | jvm | 0.318 [0.315, 0.375] (n=3) | 0.523 [0.477, 0.593] (n=3) | 9.028 [7.007, 9.275] (n=3) |
| observation_pass | service_later_mean | native | 0.295 [0.263, 0.313] (n=3) | 0.005 [0.005, 0.006] (n=3) | 0.646 [0.533, 0.657] (n=3) |
| observation_pass | service_later_mean | jvm | 0.321 [0.244, 0.375] (n=3) | 0.133 [0.112, 0.147] (n=3) | 2.130 [1.613, 2.420] (n=3) |
| mut_element_array_pass | fresh | native | 0.154 [0.143, 0.168] (n=3) | 0.009 [0.009, 0.010] (n=3) | 1.236 [1.017, 1.238] (n=3) |
| mut_element_array_pass | fresh | jvm | 0.137 [0.129, 0.139] (n=3) | 0.405 [0.404, 0.585] (n=3) | 10.910 [5.816, 10.997] (n=3) |
| mut_element_array_pass | service_first | native | 0.134 [0.125, 0.137] (n=3) | 0.008 [0.008, 0.008] (n=3) | 1.076 [0.996, 1.127] (n=3) |
| mut_element_array_pass | service_first | jvm | 0.155 [0.152, 0.385] (n=3) | 0.580 [0.432, 0.681] (n=3) | 10.558 [6.049, 10.594] (n=3) |
| mut_element_array_pass | service_later_mean | native | 0.135 [0.124, 0.136] (n=3) | 0.006 [0.006, 0.010] (n=3) | 0.886 [0.869, 0.981] (n=3) |
| mut_element_array_pass | service_later_mean | jvm | 0.161 [0.148, 0.195] (n=3) | 0.225 [0.139, 0.293] (n=3) | 3.427 [2.330, 3.936] (n=3) |
| mut_element_option_pass | fresh | native | 0.366 [0.356, 0.388] (n=3) | 0.010 [0.010, 0.010] (n=3) | 2.192 [2.090, 2.547] (n=3) |
| mut_element_option_pass | fresh | jvm | 0.374 [0.340, 0.565] (n=3) | 0.570 [0.449, 1.024] (n=3) | 7.714 [7.479, 12.968] (n=3) |
| mut_element_option_pass | service_first | native | 0.461 [0.439, 0.488] (n=3) | 0.014 [0.013, 0.027] (n=3) | 3.356 [2.769, 3.605] (n=3) |
| mut_element_option_pass | service_first | jvm | 0.374 [0.348, 0.414] (n=3) | 0.458 [0.440, 0.953] (n=3) | 8.836 [7.612, 11.469] (n=3) |
| mut_element_option_pass | service_later_mean | native | 0.435 [0.355, 0.467] (n=3) | 0.014 [0.011, 0.016] (n=3) | 2.590 [2.284, 2.757] (n=3) |
| mut_element_option_pass | service_later_mean | jvm | 0.452 [0.351, 0.521] (n=3) | 0.211 [0.186, 0.246] (n=3) | 4.491 [3.528, 5.235] (n=3) |
| mut_element_array_wrong | fresh | native | 0.132 [0.130, 0.147] (n=3) | 0.009 [0.008, 0.009] (n=3) | 1.231 [1.180, 1.425] (n=3) |
| mut_element_array_wrong | fresh | jvm | 0.154 [0.127, 0.167] (n=3) | 0.437 [0.431, 0.457] (n=3) | 9.972 [5.679, 10.338] (n=3) |
| mut_element_array_wrong | service_first | native | 0.178 [0.145, 0.179] (n=3) | 0.008 [0.007, 0.008] (n=3) | 1.286 [1.269, 1.492] (n=3) |
| mut_element_array_wrong | service_first | jvm | 0.169 [0.127, 0.175] (n=3) | 0.484 [0.469, 0.593] (n=3) | 6.424 [6.070, 10.863] (n=3) |
| mut_element_array_wrong | service_later_mean | native | 0.133 [0.133, 0.233] (n=3) | 0.007 [0.006, 0.008] (n=3) | 1.526 [1.114, 1.577] (n=3) |
| mut_element_array_wrong | service_later_mean | jvm | 0.158 [0.137, 0.161] (n=3) | 0.155 [0.143, 0.158] (n=3) | 3.417 [2.679, 3.650] (n=3) |

Worker and branch ratios below compare median paired-index wall ratios across **separate randomized blocks**, not within a single process. Ratios above one mean the numerator setting took longer. Every cell reports median [range] and valid paired count.

| Case | Backend | Mode | workers 2/1, branch off | workers 4/1, branch off | workers 2/1, branch on | workers 4/1, branch on | branch on/off, w1 | branch on/off, w2 | branch on/off, w4 |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| observation_pass | native | fresh | 1.298 [1.282, 1.487] (n=3) | 1.346 [1.204, 1.618] (n=3) | 1.005 [0.966, 1.027] (n=3) | 1.650 [1.511, 1.745] (n=3) | 1.063 [0.989, 1.083] (n=3) | 0.793 [0.690, 0.838] (n=3) | 1.111 [1.084, 1.569] (n=3) |
| observation_pass | native | service_first | 1.026 [0.887, 1.063] (n=3) | 1.130 [0.982, 1.492] (n=3) | 1.138 [1.025, 1.369] (n=3) | 1.139 [1.108, 1.307] (n=3) | 1.069 [0.878, 1.166] (n=3) | 1.293 [1.030, 1.355] (n=3) | 0.991 [0.816, 1.349] (n=3) |
| observation_pass | native | service_later_mean | 1.148 [0.899, 1.186] (n=3) | 1.217 [1.067, 1.260] (n=3) | 0.988 [0.876, 1.000] (n=3) | 0.948 [0.947, 1.024] (n=3) | 1.280 [1.264, 1.351] (n=3) | 1.139 [0.964, 1.406] (n=3) | 1.098 [0.984, 1.137] (n=3) |
| observation_pass | jvm | fresh | 1.352 [1.234, 1.803] (n=3) | 1.049 [0.823, 1.815] (n=3) | 1.024 [1.009, 1.035] (n=3) | 1.521 [1.114, 2.049] (n=3) | 0.942 [0.798, 1.059] (n=3) | 0.611 [0.593, 0.782] (n=3) | 1.081 [1.064, 1.537] (n=3) |
| observation_pass | jvm | service_first | 0.860 [0.559, 1.204] (n=3) | 0.679 [0.622, 0.964] (n=3) | 1.063 [1.007, 1.733] (n=3) | 1.089 [0.984, 1.111] (n=3) | 0.673 [0.546, 1.058] (n=3) | 1.038 [0.969, 1.237] (n=3) | 1.101 [0.617, 1.673] (n=3) |
| observation_pass | jvm | service_later_mean | 1.251 [0.775, 1.270] (n=3) | 1.114 [0.988, 1.502] (n=3) | 1.043 [0.966, 1.312] (n=3) | 1.079 [1.049, 1.110] (n=3) | 1.040 [0.699, 1.177] (n=3) | 0.966 [0.803, 1.183] (n=3) | 0.870 [0.763, 0.979] (n=3) |
| mut_element_array_pass | native | fresh | 1.113 [0.752, 1.167] (n=3) | 0.888 [0.799, 1.165] (n=3) | 1.019 [0.895, 1.224] (n=3) | 1.126 [0.952, 1.302] (n=3) | 0.912 [0.857, 1.273] (n=3) | 1.023 [0.747, 1.485] (n=3) | 1.230 [1.087, 1.256] (n=3) |
| mut_element_array_pass | native | service_first | 1.265 [1.094, 1.318] (n=3) | 1.244 [1.181, 1.359] (n=3) | 1.115 [0.756, 1.251] (n=3) | 1.063 [0.756, 1.175] (n=3) | 1.078 [0.939, 1.505] (n=3) | 0.957 [0.899, 1.024] (n=3) | 0.887 [0.843, 0.963] (n=3) |
| mut_element_array_pass | native | service_later_mean | 1.356 [0.817, 1.418] (n=3) | 1.232 [0.889, 1.263] (n=3) | 1.093 [0.972, 1.271] (n=3) | 1.271 [1.016, 1.303] (n=3) | 1.224 [0.867, 1.229] (n=3) | 1.030 [0.943, 1.152] (n=3) | 1.263 [0.989, 1.270] (n=3) |
| mut_element_array_pass | jvm | fresh | 0.916 [0.611, 0.965] (n=3) | 0.621 [0.572, 1.062] (n=3) | 1.027 [0.954, 1.612] (n=3) | 1.402 [1.030, 1.663] (n=3) | 0.622 [0.580, 1.073] (n=3) | 1.203 [0.614, 1.528] (n=3) | 1.416 [0.962, 1.809] (n=3) |
| mut_element_array_pass | jvm | service_first | 0.598 [0.586, 1.531] (n=3) | 0.601 [0.580, 0.976] (n=3) | 0.966 [0.580, 1.609] (n=3) | 1.036 [0.979, 1.564] (n=3) | 1.022 [0.620, 1.050] (n=3) | 1.040 [1.003, 1.074] (n=3) | 1.638 [1.047, 1.810] (n=3) |
| mut_element_array_pass | jvm | service_later_mean | 0.961 [0.637, 1.084] (n=3) | 0.762 [0.651, 1.012] (n=3) | 1.245 [0.907, 1.627] (n=3) | 1.229 [0.878, 1.488] (n=3) | 0.813 [0.580, 1.079] (n=3) | 1.240 [0.767, 1.481] (n=3) | 1.311 [0.937, 1.327] (n=3) |
| mut_element_option_pass | native | fresh | 1.129 [0.984, 1.133] (n=3) | 1.259 [1.174, 1.606] (n=3) | 0.893 [0.830, 0.931] (n=3) | 1.101 [0.929, 1.120] (n=3) | 1.348 [1.089, 1.680] (n=3) | 1.062 [1.030, 1.234] (n=3) | 0.971 [0.953, 1.286] (n=3) |
| mut_element_option_pass | native | service_first | 0.695 [0.688, 0.811] (n=3) | 0.856 [0.748, 0.929] (n=3) | 0.774 [0.750, 0.788] (n=3) | 0.776 [0.656, 0.803] (n=3) | 1.129 [1.104, 1.215] (n=3) | 1.253 [1.077, 1.325] (n=3) | 1.023 [0.968, 1.051] (n=3) |
| mut_element_option_pass | native | service_later_mean | 1.006 [0.972, 1.077] (n=3) | 1.174 [1.051, 1.230] (n=3) | 0.883 [0.859, 1.012] (n=3) | 0.812 [0.685, 0.964] (n=3) | 1.365 [1.019, 1.530] (n=3) | 1.239 [0.958, 1.307] (n=3) | 0.935 [0.852, 0.945] (n=3) |
| mut_element_option_pass | jvm | fresh | 1.037 [0.813, 1.048] (n=3) | 1.163 [0.972, 1.431] (n=3) | 0.859 [0.656, 0.911] (n=3) | 1.172 [1.006, 1.280] (n=3) | 1.142 [0.633, 1.705] (n=3) | 0.947 [0.709, 1.067] (n=3) | 1.151 [0.833, 1.199] (n=3) |
| mut_element_option_pass | jvm | service_first | 0.967 [0.898, 1.115] (n=3) | 0.929 [0.624, 1.603] (n=3) | 0.966 [0.878, 0.985] (n=3) | 0.985 [0.955, 1.031] (n=3) | 0.948 [0.682, 0.995] (n=3) | 0.928 [0.591, 1.013] (n=3) | 0.974 [0.640, 1.077] (n=3) |
| mut_element_option_pass | jvm | service_later_mean | 0.784 [0.776, 1.138] (n=3) | 0.982 [0.728, 1.035] (n=3) | 0.950 [0.818, 1.002] (n=3) | 0.899 [0.861, 0.952] (n=3) | 0.818 [0.748, 1.190] (n=3) | 0.966 [0.856, 0.991] (n=3) | 0.924 [0.793, 0.990] (n=3) |
| mut_element_array_wrong | native | fresh | 1.023 [0.950, 1.296] (n=3) | 1.237 [1.078, 1.252] (n=3) | 0.869 [0.818, 1.047] (n=3) | 0.831 [0.830, 0.951] (n=3) | 1.294 [1.095, 1.519] (n=3) | 1.019 [0.943, 1.324] (n=3) | 0.858 [0.842, 1.171] (n=3) |
| mut_element_array_wrong | native | service_first | 0.960 [0.955, 1.299] (n=3) | 1.018 [0.972, 1.085] (n=3) | 0.778 [0.743, 0.961] (n=3) | 0.888 [0.820, 1.069] (n=3) | 1.268 [0.931, 1.634] (n=3) | 0.933 [0.759, 1.271] (n=3) | 1.025 [0.959, 1.425] (n=3) |
| mut_element_array_wrong | native | service_later_mean | 0.915 [0.847, 1.055] (n=3) | 0.917 [0.851, 1.107] (n=3) | 1.144 [0.939, 1.196] (n=3) | 1.097 [0.993, 1.365] (n=3) | 1.060 [0.795, 1.061] (n=3) | 1.088 [1.074, 1.201] (n=3) | 1.148 [1.026, 1.306] (n=3) |
| mut_element_array_wrong | jvm | fresh | 0.772 [0.672, 1.806] (n=3) | 0.690 [0.686, 1.158] (n=3) | 0.955 [0.649, 1.616] (n=3) | 0.674 [0.580, 0.906] (n=3) | 1.108 [1.048, 1.124] (n=3) | 0.991 [0.881, 1.598] (n=3) | 0.945 [0.867, 1.029] (n=3) |
| mut_element_array_wrong | jvm | service_first | 0.925 [0.593, 1.707] (n=3) | 1.078 [0.931, 1.284] (n=3) | 0.976 [0.561, 1.017] (n=3) | 1.057 [0.974, 1.202] (n=3) | 1.030 [0.901, 1.032] (n=3) | 0.976 [0.589, 0.990] (n=3) | 0.964 [0.932, 1.023] (n=3) |
| mut_element_array_wrong | jvm | service_later_mean | 1.049 [0.758, 1.186] (n=3) | 0.956 [0.813, 1.175] (n=3) | 0.973 [0.881, 1.219] (n=3) | 1.029 [0.960, 1.182] (n=3) | 0.892 [0.782, 0.979] (n=3) | 0.907 [0.662, 1.258] (n=3) | 0.923 [0.897, 1.053] (n=3) |

Service launch-to-socket readiness is recorded **once per backend service block**, separate from requests. Socket readiness does not prove verifier or solver initialization. The table shows one-worker, branch-off medians and ranges; all configurations are retained in JSON. The JVM service keeps a process-level Viper/JVM object via `OnceLock`, while both backends construct verifier/frontend state per request. A repeated “JVM startup” stopwatch label is not evidence of a new JVM.

| Case | Native startup s | JVM startup s |
| --- | ---: | ---: |
| observation_pass | 0.051 [0.051, 0.051] (n=3) | 0.051 [0.051, 0.051] (n=3) |
| mut_element_array_pass | 0.051 [0.051, 0.052] (n=3) | 0.051 [0.051, 0.102] (n=3) |
| mut_element_option_pass | 0.051 [0.051, 0.051] (n=3) | 0.051 [0.051, 0.051] (n=3) |
| mut_element_array_wrong | 0.051 [0.051, 0.051] (n=3) | 0.051 [0.051, 0.051] (n=3) |

Service client CPU does not include the still-running server or its Z3 processes. Worker and solver durations overlap and cannot be subtracted from request wall to infer exclusive symbolic execution. Fresh process does not clear OS page caches, and hashing/copying/cleaning occurs outside the timed command. These are three paired observations per condition on the recorded host; they are not a universal speed claim. See the manifest and per-request host snapshots for load and configuration, and report censored or invalid observations alongside any comparison.
