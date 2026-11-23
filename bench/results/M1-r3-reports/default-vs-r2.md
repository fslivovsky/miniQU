# Paired comparison: B (M1-r3-default-s1, M1-r3-default-s2, M1-r3-default-s3) against A (M1-r2-default-s1, M1-r2-default-s2, M1-r2-default-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | 25216c2 | 30bd8fe6b956 | 2026-11-23T13:40:40 |
| B | `` | 46874d9 | 006221175f2f | 2026-11-23T20:12:40 |

Order in which the runs started:

- 2026-11-23T13:40:40 `M1-r2-default-s1`
- 2026-11-23T13:46:42 `M1-r2-default-s2`
- 2026-11-23T13:52:43 `M1-r2-default-s3`
- 2026-11-23T20:12:40 `M1-r3-default-s1`
- 2026-11-23T20:18:43 `M1-r3-default-s2`
- 2026-11-23T20:24:43 `M1-r3-default-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-0.24 s**, 95% bootstrap interval [-0.47, -0.05] (10000 resamples).

Sign test: B wins on 15 instances, loses on 0, ties on 361; two-sided p = 0.0001 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is better than A.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 101 | 0.988 | 59 | 41 |
| 2 | 100 | 0.964 | 51 | 49 |
| 3 | 98 | 0.942 | 58 | 40 |
| all (per instance) | 120 | 0.972 | 66 | 54 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 2 | 0.913 |  |
| DW | 6 | 0.752 |  |
| DWs | 1 | 1.039 |  |
| Lights | 1 | 0.903 |  |
| amba | 1 | 1.015 |  |
| arbiter | 2 | 0.949 |  |
| bt | 5 | 0.998 |  |
| chess | 16 | 0.883 |  |
| ci | 3 | 1.032 |  |
| collector | 1 | 0.957 |  |
| connect | 2 | 1.004 |  |
| eequery | 1 | 0.996 |  |
| finding | 1 | 0.944 |  |
| hadw | 5 | 0.870 |  |
| jctc | 6 | 1.178 | > 1.10 |
| klieber | 24 | 1.019 |  |
| lift | 1 | 0.974 |  |
| load | 1 | 0.983 |  |
| ltl | 1 | 0.896 |  |
| mult | 1 | 0.997 |  |
| numeric | 15 | 0.985 |  |
| reachqu | 2 | 1.013 |  |
| robot | 1 | 1.008 |  |
| round | 1 | 0.964 |  |
| sc | 5 | 1.030 |  |
| test | 15 | 1.007 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| jctc10-fail.qcir | 1.748 | 5.82 | 10.27 |
| jctc2-pass.qcir | 1.576 | 2.61 | 4.12 |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 1.104 | 1.08 | 1.19 |
| 9.2.qcir | 1.072 | 18.39 | 19.71 |
| sc-ungrounded-2x1X1x2_2.qcir | 1.066 | 6.88 | 7.37 |
| sc-ungrounded-1x3X3x2_1.qcir | 1.064 | 2.40 | 2.58 |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | 1.045 | 1.40 | 1.46 |
| reachqu_query64_1344.qcir | 1.045 | 23.85 | 24.80 |
| klieber2017q-072-18-t1.qcir | 1.045 | 42.20 | 44.16 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 1.044 | 17.94 | 18.90 |
| sc-ungrounded-1x2X2x2_2.qcir | 1.042 | 5.25 | 5.49 |
| DWs-sat-10-25-1.qcir | 1.039 | 14.03 | 14.58 |
| arbiter_with_buffer5.tlsf.qcir | 1.036 | 8.14 | 8.45 |
| klieber2017q-076-19-t1.qcir | 1.035 | 46.77 | 48.49 |
| 4.1.qcir | 1.034 | 7.08 | 7.27 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DW-sat-08-22-1.qcir | 0.596 | 2.90 | 1.71 |
| DW-sat-08-23-1.qcir | 0.601 | 2.53 | 1.50 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 0.717 | 4.12 | 3.20 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 0.735 | 18.00 | 11.77 |
| hadw9-10.qcir | 0.737 | 1.62 | 1.23 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 81/59/140 | 79.9 | 83/59/142 | 79.7 |
| 2 | 85/59/144 | 78.3 | 86/59/145 | 78.0 |
| 3 | 83/60/143 | 78.9 | 83/60/143 | 78.7 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 140-144 | 78.3-79.9 |
| B | 142-145 | 78.0-79.7 |

## Instances gained and lost in a majority of seeds

- gained by B (0): none
- lost by B (0): none

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 105.6 | 105.6 | -0.0 | 0 | 0 |
| DW | 7 | 32.5 | 30.8 | -1.7 | 5 | 0 |
| DWs | 13 | 117.3 | 117.3 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 92.2 | 80.4 | -11.8 | 1 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 100.7 | 100.8 | +0.1 | 0 | 0 |
| arbiter | 6 | 84.9 | 84.5 | -0.4 | 1 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 79.3 | 77.6 | -1.7 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 28.0 | 27.5 | -0.5 | 5 | 0 |
| ci | 30 | 100.1 | 100.1 | +0.0 | 0 | 0 |
| collector | 1 | 4.2 | 4.0 | -0.2 | 0 | 0 |
| connect | 7 | 86.8 | 86.8 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 79.3 | 79.2 | -0.1 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 10.2 | 9.6 | -0.6 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.1 | 76.0 | -0.1 | 0 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 75.6 | 75.9 | +0.3 | 0 | 0 |
| klieber | 26 | 52.1 | 52.6 | +0.5 | 0 | 0 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.7 | 60.7 | -0.0 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.8 | 98.5 | -0.3 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.9 | 111.9 | -0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 80.0 | +0.0 | 0 | 0 |
| numeric | 26 | 33.0 | 32.1 | -0.9 | 1 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 87.9 | 88.1 | +0.2 | 0 | 0 |
| robot | 1 | 3.9 | 3.9 | +0.0 | 0 | 0 |
| round | 1 | 1.9 | 1.8 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 57.4 | 57.5 | +0.0 | 0 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 44.4 | 44.5 | +0.0 | 0 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| Lights2_0f5381e9.tlsf.qcir | 64.3 | 40.8 | -23.6 |
| 5.2-1.qcir | 57.6 | 35.9 | -21.8 |
| bt2nd-3x4_12.ig.qcir | 95.6 | 75.4 | -20.2 |
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 41.1 | 32.5 | -8.6 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 18.0 | 11.8 | -6.3 |
| DW-unsat-09-22-1.qcir | 19.9 | 15.9 | -4.0 |
| DW-unsat-09-23-1.qcir | 25.7 | 22.0 | -3.7 |
| arbiter_on_inpchange5.tlsf.qcir | 21.3 | 18.4 | -2.8 |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 9.7 | 8.2 | -1.6 |
| ltl2dba_beta6.tlsf.qcir | 14.0 | 12.5 | -1.6 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc10-fail.qcir | 43.9 | 46.9 | +3.0 |
| klieber2017q-072-18-t1.qcir | 42.2 | 44.2 | +2.0 |
| 9.2.qcir | 18.4 | 19.7 | +1.3 |
| klieber2017q-076-19-t1.qcir | 71.2 | 72.3 | +1.1 |
| klieber2017q-078-19-t1.qcir | 48.7 | 49.8 | +1.1 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 18.0 | 18.9 | +1.0 |
| klieber2017q-064-16-t1.qcir | 29.5 | 30.5 | +0.9 |
| klieber2017q-084-21-t1.qcir | 28.1 | 29.1 | +0.9 |
| klieber2017q-082-20-t1.qcir | 22.3 | 23.1 | +0.7 |
| klieber2017q-072-18-eq.qcir | 32.6 | 33.3 | +0.7 |

## Peak memory

0 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

