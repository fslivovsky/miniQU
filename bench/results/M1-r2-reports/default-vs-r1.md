# Paired comparison: B (M1-r2-default-s1, M1-r2-default-s2, M1-r2-default-s3) against A (M1-r1-default-s1, M1-r1-default-s2, M1-r1-default-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | 00eb7a4 | a48a1a946f47 | 2026-11-23T01:09:59 |
| B | `` | 25216c2 | 30bd8fe6b956 | 2026-11-23T13:40:40 |

Order in which the runs started:

- 2026-11-23T01:09:59 `M1-r1-default-s1`
- 2026-11-23T01:33:52 `M1-r1-default-s2`
- 2026-11-23T01:57:44 `M1-r1-default-s3`
- 2026-11-23T13:40:40 `M1-r2-default-s1`
- 2026-11-23T13:46:42 `M1-r2-default-s2`
- 2026-11-23T13:52:43 `M1-r2-default-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-0.34 s**, 95% bootstrap interval [-0.68, -0.13] (10000 resamples).

Sign test: B wins on 7 instances, loses on 2, ties on 367; two-sided p = 0.1797 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is better than A.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 100 | 0.943 | 15 | 85 |
| 2 | 100 | 0.954 | 19 | 81 |
| 3 | 99 | 0.961 | 17 | 82 |
| all (per instance) | 119 | 0.950 | 12 | 107 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 2 | 0.901 |  |
| DW | 6 | 0.887 |  |
| DWs | 1 | 0.831 |  |
| Lights | 1 | 1.045 |  |
| amba | 1 | 0.987 |  |
| arbiter | 2 | 1.002 |  |
| bt | 4 | 0.979 |  |
| chess | 16 | 0.937 |  |
| ci | 3 | 0.981 |  |
| collector | 1 | 0.916 |  |
| connect | 2 | 0.981 |  |
| eequery | 1 | 0.994 |  |
| finding | 1 | 0.962 |  |
| hadw | 5 | 0.975 |  |
| jctc | 6 | 0.851 |  |
| klieber | 24 | 0.964 |  |
| lift | 1 | 0.926 |  |
| load | 1 | 0.969 |  |
| ltl | 1 | 0.922 |  |
| mult | 1 | 0.977 |  |
| numeric | 15 | 0.942 |  |
| reachqu | 2 | 0.969 |  |
| robot | 1 | 0.950 |  |
| round | 1 | 0.958 |  |
| sc | 5 | 0.930 |  |
| test | 15 | 0.994 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 1.172 | 35.32 | 41.10 |
| Lights2_0f5381e9.tlsf.qcir | 1.045 | 34.87 | 36.42 |
| DW-sat-08-22-1.qcir | 1.032 | 2.84 | 2.90 |
| arbiter_on_inpchange5.tlsf.qcir | 1.028 | 20.74 | 21.24 |
| hadw2-7.qcir | 1.022 | 14.56 | 14.90 |
| 5.2-1.qcir | 1.016 | 26.04 | 26.44 |
| jctc9-pass.qcir | 1.012 | 5.88 | 5.95 |
| jctc6-pass.qcir | 1.008 | 17.55 | 17.70 |
| hadw9-10.qcir | 1.007 | 1.53 | 1.62 |
| test_5_5_tippy.pg-9.qcir | 1.006 | 26.68 | 26.85 |
| test_5_5_skinny.pg-9.qcir | 1.002 | 44.09 | 44.18 |
| test_5_5_elly.pg-7.qcir | 1.001 | 1.23 | 1.23 |
| test_5_5_knobby.pg-9.qcir | 0.999 | 41.26 | 41.24 |
| test_5_5_fatty.pg-9.qcir | 0.997 | 37.43 | 37.38 |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | 0.997 | 1.12 | 1.12 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| jctc2-pass.qcir | 0.549 | 4.76 | 2.61 |
| DW-unsat-09-23-1.qcir | 0.766 | 34.71 | 25.65 |
| DW-unsat-09-22-1.qcir | 0.792 | 25.19 | 19.85 |
| DWs-sat-10-25-1.qcir | 0.831 | 16.89 | 14.03 |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 0.839 | 1.29 | 1.08 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 81/57/138 | 80.5 | 81/59/140 | 79.9 |
| 2 | 85/58/143 | 78.6 | 85/59/144 | 78.3 |
| 3 | 83/60/143 | 79.0 | 83/60/143 | 78.9 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 138-143 | 78.6-80.5 |
| B | 140-144 | 78.3-79.9 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `DW-unsat-10-25-1.qcir`
- lost by B (0): none

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 105.7 | 105.6 | -0.1 | 0 | 0 |
| DW | 7 | 41.5 | 32.5 | -9.0 | 3 | 0 |
| DWs | 13 | 117.4 | 117.3 | -0.1 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 91.6 | 92.2 | +0.5 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 100.8 | 100.7 | -0.1 | 0 | 0 |
| arbiter | 6 | 84.9 | 84.9 | +0.0 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 81.1 | 79.3 | -1.8 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 28.0 | 28.0 | -0.0 | 2 | 2 |
| ci | 30 | 100.1 | 100.1 | -0.0 | 0 | 0 |
| collector | 1 | 4.6 | 4.2 | -0.4 | 0 | 0 |
| connect | 7 | 86.8 | 86.8 | -0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 79.4 | 79.3 | -0.1 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 10.6 | 10.2 | -0.4 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.2 | 76.1 | -0.0 | 0 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 75.8 | 75.6 | -0.2 | 0 | 0 |
| klieber | 26 | 53.1 | 52.1 | -0.9 | 0 | 0 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.8 | 60.7 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 99.1 | 98.8 | -0.3 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 112.0 | 111.9 | -0.1 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 80.0 | +0.0 | 0 | 0 |
| numeric | 26 | 33.3 | 33.0 | -0.3 | 1 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 88.1 | 87.9 | -0.2 | 0 | 0 |
| robot | 1 | 4.1 | 3.9 | -0.2 | 0 | 0 |
| round | 1 | 2.0 | 1.9 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 57.7 | 57.4 | -0.3 | 0 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 44.5 | 44.4 | -0.0 | 0 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| DW-unsat-10-25-1.qcir | 99.5 | 51.6 | -47.9 |
| bt-2x5_17.ig.qcir | 120.0 | 99.8 | -20.2 |
| DW-unsat-09-23-1.qcir | 34.7 | 25.7 | -9.1 |
| DW-unsat-09-22-1.qcir | 25.2 | 19.9 | -5.3 |
| klieber2017q-072-18-t1.qcir | 45.7 | 42.2 | -3.5 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 21.0 | 18.0 | -3.0 |
| 9.2.qcir | 20.5 | 18.4 | -2.1 |
| 11.1.qcir | 34.4 | 32.5 | -1.9 |
| klieber2017q-078-19-t1.qcir | 50.5 | 48.7 | -1.8 |
| klieber2017q-064-16-t1.qcir | 31.4 | 29.5 | -1.8 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 35.4 | 41.1 | +5.8 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 15.9 | 18.0 | +2.2 |
| Lights2_0f5381e9.tlsf.qcir | 63.3 | 64.3 | +1.0 |
| arbiter_on_inpchange5.tlsf.qcir | 20.8 | 21.3 | +0.5 |
| hadw2-7.qcir | 14.6 | 14.9 | +0.3 |
| 5.2-1.qcir | 57.4 | 57.6 | +0.3 |
| test_5_5_tippy.pg-9.qcir | 26.7 | 26.9 | +0.2 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 11.0 | 11.1 | +0.1 |
| hadw9-10.qcir | 1.5 | 1.6 | +0.1 |
| test_5_5_skinny.pg-9.qcir | 44.1 | 44.2 | +0.1 |

## Peak memory

0 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

