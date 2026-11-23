# Paired comparison: B (M1-r2-mode1-s1) against A (baseline-c96-mode1-t60-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=1` | c39005a | 10ff614c6694 | 2026-11-23T02:27:56 |
| B | `-mode=1` | 25216c2 | 30bd8fe6b956 | 2026-11-23T14:16:26 |

Order in which the runs started:

- 2026-11-23T02:27:56 `baseline-c96-mode1-t60-s1`
- 2026-11-23T14:16:26 `M1-r2-mode1-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **+0.41 s**, 95% bootstrap interval [-1.02, +1.88] (10000 resamples).

Sign test: B wins on 18 instances, loses on 21, ties on 337; two-sided p = 0.7493 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 35 | 1.063 | 25 | 10 |
| all (per instance) | 35 | 1.063 | 25 | 10 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 5 | 1.260 | > 1.10 |
| chess | 11 | 1.119 | > 1.10 |
| collector | 1 | 1.016 |  |
| hadw | 2 | 1.235 |  |
| lift | 1 | 0.895 |  |
| ltl | 1 | 1.032 |  |
| numeric | 13 | 0.958 |  |
| round | 1 | 0.955 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 1.657 | 10.41 | 17.25 |
| DW-sat-08-23-1.qcir | 1.606 | 1.70 | 2.73 |
| DW-unsat-09-22-1.qcir | 1.431 | 12.10 | 17.30 |
| DW-sat-08-22-1.qcir | 1.319 | 2.03 | 2.68 |
| hadw10-11.qcir | 1.285 | 1.45 | 1.87 |
| 5.2-1.qcir | 1.277 | 28.50 | 36.40 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 1.239 | 2.12 | 2.62 |
| hadw11-12.qcir | 1.187 | 8.53 | 10.13 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 1.183 | 14.63 | 17.31 |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 1.145 | 2.60 | 2.98 |
| 4.1.qcir | 1.114 | 7.24 | 8.06 |
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 1.102 | 36.74 | 40.48 |
| 11.1.qcir | 1.073 | 32.82 | 35.20 |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | 1.072 | 1.06 | 1.14 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 1.069 | 18.27 | 19.53 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 3.2.qcir | 0.748 | 1.16 | 0.87 |
| 10.2.qcir | 0.766 | 1.64 | 1.25 |
| 9.1.qcir | 0.779 | 2.16 | 1.69 |
| 1.3.qcir | 0.856 | 7.78 | 6.66 |
| 10.1.qcir | 0.887 | 2.17 | 1.93 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 72/44/116 | 85.9 | 70/44/114 | 86.3 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 116-116 | 85.9-85.9 |
| B | 114-114 | 86.3-86.3 |

## Instances gained and lost in a majority of seeds

- gained by B (4): `CM-sat-04-01-06-3.qcir`, `jctc14-unrolled-fail.qcir`, `jctc8-pass.qcir`, `reachqu_query64_1344.qcir`
- lost by B (6): `5.1-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `hadw6-8.qcir`, `klieber2017q-072-18-eq.qcir`, `reachqu_query60_1344.qcir`, `test_5_5_elly.pg-9.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 120.0 | 103.1 | -16.9 | 1 | 0 |
| DW | 7 | 40.2 | 41.3 | +1.1 | 0 | 2 |
| DWs | 13 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 89.7 | 120.0 | +30.3 | 0 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.4 | 101.5 | +0.1 | 0 | 0 |
| arbiter | 6 | 85.0 | 85.2 | +0.2 | 0 | 1 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 92.5 | 93.7 | +1.3 | 0 | 1 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 29.3 | 29.9 | +0.6 | 0 | 5 |
| ci | 30 | 100.1 | 100.1 | -0.1 | 1 | 0 |
| collector | 1 | 3.5 | 3.5 | +0.0 | 0 | 0 |
| connect | 7 | 89.1 | 89.1 | -0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 71.2 | 71.8 | +0.7 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 11.7 | 11.7 | -0.0 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 69.2 | 72.2 | +3.0 | 2 | 2 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.9 | 70.8 | -13.0 | 3 | 0 |
| klieber | 26 | 112.1 | 116.5 | +4.4 | 0 | 2 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.2 | 61.0 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.3 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 97.8 | 97.8 | +0.1 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.3 | 110.8 | +0.5 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 31.3 | 34.4 | +3.1 | 1 | 2 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 83.3 | 91.5 | +8.2 | 1 | 1 |
| robot | 1 | 4.5 | 4.0 | -0.5 | 0 | 0 |
| round | 1 | 1.5 | 1.5 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 58.2 | 56.8 | -1.4 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 68.6 | 70.7 | +2.1 | 6 | 3 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | 120.0 | 1.9 | -118.1 |
| jctc8-pass.qcir | 120.0 | 32.9 | -87.1 |
| reachqu_query64_1344.qcir | 120.0 | 34.5 | -85.5 |
| jctc14-unrolled-fail.qcir | 120.0 | 40.3 | -79.7 |
| sc-ungrounded-2x2X2x2_1.qcir | 26.4 | 16.7 | -9.7 |
| test_5_5_snaky.pg-7.qcir | 15.7 | 7.3 | -8.4 |
| test_5_5_Z.pg-7.qcir | 14.7 | 6.3 | -8.4 |
| hadw4-7.qcir | 59.9 | 53.0 | -7.0 |
| test_5_5_domino.pg-11.qcir | 10.7 | 4.1 | -6.5 |
| test_5_5_knobby.pg-7.qcir | 9.5 | 7.0 | -2.4 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| reachqu_query60_1344.qcir | 9.8 | 120.0 | +110.2 |
| klieber2017q-072-18-eq.qcir | 20.7 | 120.0 | +99.3 |
| test_5_5_elly.pg-9.qcir | 46.9 | 120.0 | +73.1 |
| 5.1-1.qcir | 50.0 | 120.0 | +70.0 |
| hadw6-8.qcir | 51.1 | 120.0 | +68.9 |
| Lights2_0f5381e9.tlsf.qcir | 59.5 | 120.0 | +60.5 |
| klieber2017q-060-15-eq.qcir | 13.3 | 28.7 | +15.4 |
| bt2nd-2x5_10.ig.qcir | 28.0 | 42.5 | +14.5 |
| test_5_5_elly.pg-7.qcir | 1.6 | 10.5 | +8.9 |
| 5.2-1.qcir | 28.6 | 36.4 | +7.9 |

## Peak memory

0 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

