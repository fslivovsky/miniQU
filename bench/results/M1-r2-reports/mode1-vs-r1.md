# Paired comparison: B (M1-r2-mode1-s1) against A (M1-r1-mode1-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=1` | 00eb7a4 | a48a1a946f47 | 2026-11-23T02:21:44 |
| B | `-mode=1` | 25216c2 | 30bd8fe6b956 | 2026-11-23T14:16:26 |

Order in which the runs started:

- 2026-11-23T02:21:44 `M1-r1-mode1-s1`
- 2026-11-23T14:16:26 `M1-r2-mode1-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-0.04 s**, 95% bootstrap interval [-0.31, +0.37] (10000 resamples).

Sign test: B wins on 10 instances, loses on 1, ties on 365; two-sided p = 0.0117 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 76 | 0.933 | 7 | 69 |
| all (per instance) | 76 | 0.933 | 7 | 69 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 1 | 0.987 |  |
| DW | 5 | 0.932 |  |
| amba | 1 | 0.990 |  |
| arbiter | 2 | 0.986 |  |
| bt | 2 | 0.982 |  |
| chess | 16 | 0.916 |  |
| collector | 1 | 0.953 |  |
| connect | 2 | 0.975 |  |
| eequery | 1 | 0.964 |  |
| finding | 1 | 0.864 |  |
| hadw | 6 | 0.949 |  |
| jctc | 4 | 0.779 |  |
| klieber | 1 | 0.950 |  |
| lift | 1 | 0.908 |  |
| load | 1 | 0.958 |  |
| ltl | 1 | 0.905 |  |
| mult | 1 | 0.984 |  |
| numeric | 12 | 0.952 |  |
| reachqu | 1 | 0.906 |  |
| robot | 1 | 0.993 |  |
| round | 1 | 0.979 |  |
| sc | 5 | 0.896 |  |
| test | 9 | 0.972 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.265 | 2.12 | 2.68 |
| hadw9-10.qcir | 1.096 | 1.24 | 1.35 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 1.060 | 2.47 | 2.62 |
| jctc8-pass.qcir | 1.045 | 31.44 | 32.86 |
| 5.2-1.qcir | 1.028 | 35.39 | 36.40 |
| hadw11-12.qcir | 1.011 | 10.02 | 10.13 |
| arbiter_on_inpchange5.tlsf.qcir | 1.008 | 19.98 | 20.14 |
| robot_grid6_1.tlsf.qcir | 0.993 | 3.97 | 3.95 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 0.993 | 41.78 | 41.47 |
| amba2c7n.sat.qcir | 0.990 | 27.83 | 27.57 |
| CM-sat-04-01-06-3.qcir | 0.987 | 1.84 | 1.82 |
| sc-ungrounded-1x2X2x2_2.qcir | 0.986 | 5.50 | 5.43 |
| mult9.sat.qcir | 0.984 | 37.51 | 36.91 |
| bt2nd-2x5_10.ig.qcir | 0.982 | 43.21 | 42.43 |
| bt-2x4_13.ig.qcir | 0.982 | 1.84 | 1.80 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| jctc2-pass.qcir | 0.555 | 7.72 | 4.28 |
| jctc14-unrolled-fail.qcir | 0.674 | 59.71 | 40.24 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 0.778 | 6.95 | 5.41 |
| DW-unsat-09-23-1.qcir | 0.793 | 22.90 | 18.17 |
| DW-unsat-09-22-1.qcir | 0.811 | 21.34 | 17.30 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 70/45/115 | 86.3 | 70/44/114 | 86.3 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 115-115 | 86.3-86.3 |
| B | 114-114 | 86.3-86.3 |

## Instances gained and lost in a majority of seeds

- gained by B (0): none
- lost by B (1): `hadw6-8.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 103.1 | 103.1 | +0.0 | 0 | 0 |
| DW | 7 | 42.6 | 41.3 | -1.3 | 2 | 0 |
| DWs | 13 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.6 | 101.5 | -0.1 | 0 | 0 |
| arbiter | 6 | 85.2 | 85.2 | -0.0 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 93.8 | 93.7 | -0.1 | 0 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 30.2 | 29.9 | -0.3 | 2 | 0 |
| ci | 30 | 100.1 | 100.1 | -0.0 | 0 | 0 |
| collector | 1 | 3.7 | 3.5 | -0.2 | 0 | 0 |
| connect | 7 | 89.2 | 89.1 | -0.1 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 72.3 | 71.8 | -0.4 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 13.5 | 11.7 | -1.9 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 69.4 | 72.2 | +2.7 | 1 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 72.5 | 70.8 | -1.7 | 2 | 0 |
| klieber | 26 | 116.5 | 116.5 | -0.1 | 0 | 0 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.1 | 61.0 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.0 | 97.8 | -0.2 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.8 | 110.8 | -0.1 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 34.7 | 34.4 | -0.3 | 0 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 92.7 | 91.5 | -1.2 | 1 | 0 |
| robot | 1 | 4.0 | 4.0 | -0.0 | 0 | 0 |
| round | 1 | 1.5 | 1.5 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 57.3 | 56.8 | -0.5 | 1 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 70.8 | 70.7 | -0.1 | 0 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc14-unrolled-fail.qcir | 59.7 | 40.3 | -19.5 |
| hadw4-7.qcir | 59.7 | 53.0 | -6.7 |
| DW-unsat-09-23-1.qcir | 22.9 | 18.2 | -4.7 |
| DW-unsat-09-22-1.qcir | 21.3 | 17.3 | -4.0 |
| reachqu_query64_1344.qcir | 38.1 | 34.5 | -3.6 |
| sc-ungrounded-2x2X2x2_1.qcir | 20.1 | 16.7 | -3.4 |
| jctc2-pass.qcir | 7.8 | 4.3 | -3.4 |
| 3.1.qcir | 48.7 | 45.5 | -3.2 |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 18.2 | 15.3 | -2.8 |
| 11.1.qcir | 37.3 | 35.2 | -2.0 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| hadw6-8.qcir | 55.7 | 120.0 | +64.3 |
| jctc8-pass.qcir | 31.5 | 32.9 | +1.4 |
| 5.2-1.qcir | 35.4 | 36.4 | +1.0 |
| DW-sat-08-22-1.qcir | 2.2 | 2.7 | +0.6 |
| arbiter_on_inpchange5.tlsf.qcir | 20.0 | 20.2 | +0.2 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.5 | 2.7 | +0.1 |
| hadw9-10.qcir | 1.3 | 1.4 | +0.1 |
| hadw11-12.qcir | 10.1 | 10.2 | +0.1 |
| jctc4-fail.qcir | 0.8 | 0.9 | +0.0 |
| hadw8-9.qcir | 0.5 | 0.5 | +0.0 |

## Peak memory

1 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| robot_grid6_1.tlsf.qcir | 18 | 21 | 1.15x |

