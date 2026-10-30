# Separate instrumentation profile

The separate profiling run completed 144/144 sessions, with 144 valid, zero invalid or censored, and 48/48 eligible matched blocks. Each block contains plain, phase-timed and phase-timed plus solver-accounting variants for three serial requests. The independent audit found no integrity, proof, raw diagnostic, phase, timer or accounting issues. This is a three-repetition instrumentation study, distinct from the primary plain-driver backend measurements.

All numbers below are median (minimum–maximum) across three independent matched blocks. Timing ratios compare command wall within the same block; GNU time rounds to hundredths of a second. Values near the timer resolution and the small sample size limit interpretation.

| Backend | Case | Workers / branch | Timed / plain | Accounting / timed |
| --- | --- | --- | ---: | ---: |
| native | mut_element_array_pass | 1 / off | 1.200 (0.943–1.261) | 1.004 (0.995–1.084) |
| native | mut_element_array_pass | 4 / on | 0.957 (0.769–1.013) | 1.074 (0.965–1.208) |
| native | mut_element_array_wrong | 1 / off | 1.040 (0.980–1.439) | 1.023 (1.022–1.107) |
| native | mut_element_array_wrong | 4 / on | 1.009 (1.005–1.246) | 0.964 (0.809–0.982) |
| native | mut_element_option_pass | 1 / off | 0.943 (0.757–1.395) | 1.014 (0.883–1.043) |
| native | mut_element_option_pass | 4 / on | 1.019 (0.781–1.165) | 1.008 (0.869–1.208) |
| native | observation_pass | 1 / off | 1.016 (0.897–1.024) | 0.965 (0.819–1.516) |
| native | observation_pass | 4 / on | 1.023 (0.889–1.072) | 0.946 (0.915–0.995) |
| source | mut_element_array_pass | 1 / off | 0.629 (0.570–1.548) | 0.876 (0.680–1.298) |
| source | mut_element_array_pass | 4 / on | 1.093 (1.055–1.267) | 1.446 (0.974–1.706) |
| source | mut_element_array_wrong | 1 / off | 0.995 (0.807–1.623) | 0.607 (0.590–1.651) |
| source | mut_element_array_wrong | 4 / on | 1.268 (0.666–1.671) | 1.317 (0.800–1.536) |
| source | mut_element_option_pass | 1 / off | 0.729 (0.604–1.622) | 0.867 (0.716–1.127) |
| source | mut_element_option_pass | 4 / on | 1.044 (0.623–1.261) | 1.039 (0.611–1.259) |
| source | observation_pass | 1 / off | 0.732 (0.564–0.911) | 1.018 (0.809–1.283) |
| source | observation_pass | 4 / on | 1.598 (1.266–1.856) | 0.570 (0.566–1.053) |

The overhead ratios vary substantially in this small sample, especially for the JVM. They do not establish negligible instrumentation overhead or a stable correction factor for the primary runs. Primary backend speed comparisons use the separate plain-driver experiment.

CPU values below are seconds per wrapped session; share is identified solver-process CPU divided by total accounted CPU. Probe CPU is separate. Residual includes frontend, runtime, wrappers and other processes. Foreground GNU time CPU is rounded, while adopted process CPU has finer precision; small residuals can reflect rounding. CPU totals and phases overlap in time, and no elapsed wall subtraction is used.

| Backend | Case | Workers / branch | Total CPU s | Solver CPU s | Probe CPU s | Residual CPU s | Solver share |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| native | mut_element_array_pass | 1 / off | 7.468 (5.863–7.813) | 1.058 (0.823–1.103) | 0.000 (0.000–0.000) | 6.410 (5.040–6.710) | 0.141 (0.140–0.142) |
| native | mut_element_array_pass | 4 / on | 7.705 (7.201–9.645) | 1.575 (1.461–2.015) | 0.000 (0.000–0.000) | 6.130 (5.740–7.630) | 0.204 (0.203–0.209) |
| native | mut_element_array_wrong | 1 / off | 8.761 (6.579–9.229) | 1.881 (1.409–1.959) | 0.000 (0.000–0.000) | 6.880 (5.170–7.270) | 0.214 (0.212–0.215) |
| native | mut_element_array_wrong | 4 / on | 7.788 (7.561–7.854) | 1.998 (1.871–2.014) | 0.000 (0.000–0.000) | 5.790 (5.690–5.840) | 0.256 (0.247–0.257) |
| native | mut_element_option_pass | 1 / off | 13.498 (13.038–15.538) | 2.738 (2.678–3.138) | 0.000 (0.000–0.000) | 10.760 (10.360–12.400) | 0.203 (0.202–0.205) |
| native | mut_element_option_pass | 4 / on | 15.821 (15.610–19.357) | 4.081 (3.810–5.287) | 0.000 (0.000–0.000) | 11.800 (11.740–14.070) | 0.258 (0.244–0.273) |
| native | observation_pass | 1 / off | 4.400 (4.325–6.444) | 0.530 (0.515–0.764) | 0.000 (0.000–0.000) | 3.870 (3.810–5.680) | 0.119 (0.119–0.120) |
| native | observation_pass | 4 / on | 7.428 (6.441–8.569) | 1.528 (1.471–2.009) | 0.000 (0.000–0.000) | 5.900 (4.970–6.560) | 0.228 (0.206–0.234) |
| source | mut_element_array_pass | 1 / off | 39.160 (36.511–42.185) | 1.291 (1.210–1.845) | 0.000 (0.000–0.000) | 37.950 (35.220–40.340) | 0.035 (0.031–0.044) |
| source | mut_element_array_pass | 4 / on | 60.741 (46.473–67.302) | 2.902 (2.553–3.061) | 0.000 (0.000–0.000) | 57.680 (43.920–64.400) | 0.050 (0.043–0.055) |
| source | mut_element_array_wrong | 1 / off | 37.090 (34.231–64.588) | 1.750 (1.741–2.758) | 0.000 (0.000–0.000) | 35.340 (32.490–61.830) | 0.047 (0.043–0.051) |
| source | mut_element_array_wrong | 4 / on | 65.621 (61.852–66.418) | 3.421 (2.992–3.618) | 0.000 (0.000–0.000) | 62.200 (58.860–62.800) | 0.052 (0.048–0.054) |
| source | mut_element_option_pass | 1 / off | 45.033 (39.759–52.379) | 3.019 (2.889–3.853) | 0.000 (0.000–0.000) | 41.180 (36.740–49.490) | 0.076 (0.055–0.086) |
| source | mut_element_option_pass | 4 / on | 44.495 (43.272–56.793) | 4.515 (4.452–6.233) | 0.000 (0.000–0.000) | 39.980 (38.820–50.560) | 0.103 (0.101–0.110) |
| source | observation_pass | 1 / off | 32.833 (32.547–61.310) | 0.937 (0.923–1.440) | 0.000 (0.000–0.000) | 31.910 (31.610–59.870) | 0.028 (0.023–0.029) |
| source | observation_pass | 4 / on | 36.545 (35.627–63.468) | 1.737 (1.705–2.798) | 0.000 (0.000–0.000) | 34.840 (33.890–60.670) | 0.047 (0.044–0.049) |

The timed variant’s request-total values below distinguish the first request from the mean of requests two and three within each session. All other recorded per-request phases and session boundaries, with all three values, are in the JSON. Source and native phases have different boundaries and must not be compared by name or added as if exclusive. Session phases are emitted intervals, not whole-process JVM startup.

| Backend | Case | Workers / branch | First request ms | Later request mean ms | Session phase medians ms |
| --- | --- | --- | ---: | ---: | --- |
| native | mut_element_array_pass | 1 / off | 2454.554 (2062.509–2711.827) | 2245.481 (1908.953–2477.149) | config_parse: 0.193, session_start: 14.140, session_stop: 45.727 |
| native | mut_element_array_pass | 4 / on | 2302.833 (2168.602–2940.656) | 2273.097 (2245.750–2351.900) | config_parse: 0.169, session_start: 60.245, session_stop: 83.936 |
| native | mut_element_array_wrong | 1 / off | 2789.084 (2184.718–2970.643) | 2672.749 (2116.100–2889.250) | config_parse: 0.205, session_start: 14.033, session_stop: 47.089 |
| native | mut_element_array_wrong | 4 / on | 2431.899 (2308.938–3147.939) | 2522.677 (2517.129–3025.189) | config_parse: 0.178, session_start: 61.830, session_stop: 85.996 |
| native | mut_element_option_pass | 1 / off | 4346.110 (4089.059–5789.901) | 4497.741 (4228.566–5913.065) | config_parse: 0.184, session_start: 13.064, session_stop: 62.585 |
| native | mut_element_option_pass | 4 / on | 4934.632 (4597.070–6306.330) | 4874.422 (4867.498–5276.722) | config_parse: 0.165, session_start: 61.054, session_stop: 99.209 |
| native | observation_pass | 1 / off | 1409.307 (1384.165–1477.698) | 1491.092 (1413.017–2004.949) | config_parse: 0.162, session_start: 13.615, session_stop: 32.198 |
| native | observation_pass | 4 / on | 2150.274 (1684.877–2340.658) | 2479.719 (1978.906–2700.611) | config_parse: 0.208, session_start: 64.828, session_stop: 67.537 |
| source | mut_element_array_pass | 1 / off | 6656.481 (6275.017–11647.851) | 3134.890 (2308.633–3274.577) | frontend_construct: 241.793, frontend_init: 0.029, frontend_prepare: 255.650, verifier_construct: 5.662, verifier_stop: 5.964 |
| source | mut_element_array_pass | 4 / on | 7742.758 (6472.502–10587.005) | 2329.836 (2213.443–2486.663) | frontend_construct: 268.235, frontend_init: 0.016, frontend_prepare: 347.294, verifier_construct: 7.401, verifier_stop: 10.360 |
| source | mut_element_array_wrong | 1 / off | 11521.932 (6941.525–11809.836) | 3748.203 (2734.345–3980.358) | frontend_construct: 195.120, frontend_init: 0.019, frontend_prepare: 240.546, verifier_construct: 5.720, verifier_stop: 4.965 |
| source | mut_element_array_wrong | 4 / on | 7614.531 (7219.140–14188.774) | 4228.403 (2727.934–4625.939) | frontend_construct: 280.290, frontend_init: 0.013, frontend_prepare: 376.818, verifier_construct: 8.753, verifier_stop: 12.051 |
| source | mut_element_option_pass | 1 / off | 8458.738 (8131.887–14092.215) | 3924.218 (3317.335–5173.728) | frontend_construct: 187.944, frontend_init: 0.022, frontend_prepare: 242.844, verifier_construct: 5.805, verifier_stop: 5.540 |
| source | mut_element_option_pass | 4 / on | 8455.244 (8425.257–14185.159) | 3722.140 (3291.387–5261.368) | frontend_construct: 263.954, frontend_init: 0.013, frontend_prepare: 380.670, verifier_construct: 7.783, verifier_stop: 12.576 |
| source | observation_pass | 1 / off | 6398.827 (5302.225–7809.393) | 2121.723 (1935.575–3732.511) | frontend_construct: 212.315, frontend_init: 0.019, frontend_prepare: 236.628, verifier_construct: 6.001, verifier_stop: 5.028 |
| source | observation_pass | 4 / on | 10739.659 (9639.160–11548.386) | 3819.272 (3530.385–3947.274) | frontend_construct: 232.545, frontend_init: 0.017, frontend_prepare: 255.840, verifier_construct: 5.580, verifier_stop: 14.879 |

The [machine report](performance-profile.json) preserves every structured trial, full compatibility session, per-process accounting records and hashes, block audit, and all phase metrics. Frozen artifact paths and hashes identify the local evidence; they do not prove that unobserved descendants were absent. The real accounting controls cover the documented normal and timeout cases. Solver CPU is process accounting, not exclusive symbolic execution.
