# Paired comparison: B (M1-r3-dl-s1, M1-r3-dl-s2, M1-r3-dl-s3) against A (baseline-c96-dl-t60-s1, baseline-c96-dl-t60-s2, baseline-c96-dl-t60-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | c39005a | 10ff614c6694 | 2026-11-23T01:28:03 |
| B | `-dl` | 46874d9 | 006221175f2f | 2026-11-23T20:30:44 |

Order in which the runs started:

- 2026-11-23T01:28:03 `baseline-c96-dl-t60-s1`
- 2026-11-23T01:51:49 `baseline-c96-dl-t60-s2`
- 2026-11-23T02:15:46 `baseline-c96-dl-t60-s3`
- 2026-11-23T20:30:44 `M1-r3-dl-s1`
- 2026-11-23T20:36:39 `M1-r3-dl-s2`
- 2026-11-23T20:42:30 `M1-r3-dl-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **-0.11 s**, 95% bootstrap interval [-0.82, +0.56] (10000 resamples).

Sign test: B wins on 42 instances, loses on 24, ties on 310; two-sided p = 0.0356 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 41 | 0.949 | 13 | 28 |
| 2 | 43 | 0.938 | 15 | 28 |
| 3 | 31 | 0.974 | 8 | 23 |
| all (per instance) | 51 | 0.950 | 16 | 35 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 4 | 0.932 |  |
| Lights | 2 | 1.078 |  |
| chess | 18 | 0.959 |  |
| collector | 1 | 0.882 |  |
| finding | 1 | 1.003 |  |
| hadw | 4 | 0.899 |  |
| jctc | 3 | 0.969 |  |
| lift | 1 | 0.897 |  |
| ltl | 1 | 0.893 |  |
| numeric | 14 | 0.952 |  |
| round | 1 | 0.915 |  |
| voter | 1 | 0.925 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| jctc17-vals-0,2-pass.qcir | 1.205 | 11.54 | 15.42 |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 1.183 | 15.03 | 17.78 |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | 1.152 | 4.46 | 4.38 |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | 1.140 | 5.65 | 6.44 |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | 1.123 | 3.30 | 3.80 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 1.111 | 10.94 | 12.15 |
| Lights2_b02056d6.tlsf.qcir | 1.095 | 24.76 | 26.34 |
| DW-sat-09-26-1.qcir | 1.079 | 14.46 | 15.60 |
| Lights2_0f5381e9.tlsf.qcir | 1.061 | 53.27 | 56.36 |
| 5.2-1.qcir | 1.054 | 35.44 | 37.03 |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | 1.054 | 6.59 | 6.71 |
| hadw11-12.qcir | 1.051 | 51.69 | 54.32 |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 1.027 | 8.51 | 8.53 |
| 4.1.qcir | 1.010 | 12.63 | 12.84 |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | 1.009 | 5.67 | 6.97 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | 0.747 | 4.42 | 3.27 |
| hadw10-11.qcir | 0.763 | 34.83 | 24.07 |
| DW-sat-08-23-1.qcir | 0.791 | 8.87 | 6.94 |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | 0.792 | 5.56 | 4.29 |
| 9.1.qcir | 0.793 | 2.22 | 1.76 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 84/66/150 | 76.4 | 85/64/149 | 76.5 |
| 2 | 86/67/153 | 75.7 | 88/65/153 | 75.6 |
| 3 | 84/62/146 | 77.7 | 83/63/146 | 77.4 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 146-153 | 75.7-77.7 |
| B | 146-153 | 75.6-77.4 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `CM-sat-04-01-06-3.qcir`
- lost by B (0): none

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 97.2 | 88.4 | -8.8 | 2 | 2 |
| DW | 7 | 21.4 | 18.2 | -3.2 | 4 | 0 |
| DWs | 13 | 117.8 | 120.0 | +2.2 | 0 | 1 |
| JP | 6 | 109.9 | 112.8 | +2.9 | 0 | 1 |
| Lights | 2 | 50.2 | 52.0 | +1.8 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 107.7 | 104.0 | -3.7 | 1 | 1 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 87.2 | 91.3 | +4.1 | 1 | 1 |
| arbiter | 6 | 84.2 | 83.9 | -0.2 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 80.8 | 83.5 | +2.8 | 1 | 2 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 61.8 | 62.0 | +0.2 | 4 | 2 |
| ci | 30 | 88.6 | 88.6 | +0.0 | 1 | 1 |
| collector | 1 | 4.3 | 3.8 | -0.5 | 0 | 0 |
| connect | 7 | 88.4 | 87.7 | -0.8 | 1 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 69.5 | 70.1 | +0.7 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.8 | 7.8 | -0.1 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 78.7 | 78.0 | -0.6 | 4 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 37.4 | 38.2 | +0.8 | 3 | 2 |
| klieber | 26 | 17.3 | 16.1 | -1.2 | 11 | 7 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.2 | 61.0 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 99.2 | 98.8 | -0.3 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.1 | 111.6 | +0.5 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.1 | 80.1 | -0.0 | 0 | 0 |
| numeric | 26 | 36.8 | 36.7 | -0.1 | 0 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 72.9 | 79.8 | +6.9 | 0 | 1 |
| robot | 1 | 4.4 | 3.2 | -1.2 | 1 | 0 |
| round | 1 | 1.4 | 1.3 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.7 | 56.1 | -0.6 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 38.1 | 37.3 | -0.8 | 4 | 2 |
| voter | 2 | 102.1 | 102.0 | -0.2 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | 90.4 | 23.1 | -67.3 |
| klieber2017q-084-21-eq.qcir | 68.4 | 26.7 | -41.7 |
| SR-sat-02-01-06-3.qcir | 120.0 | 89.1 | -30.9 |
| jctc10-fail.qcir | 120.0 | 89.3 | -30.7 |
| test_5_5_fatty.pg-9.qcir | 73.9 | 47.5 | -26.4 |
| CM-sat-07-01-07-3.qcir | 120.0 | 96.9 | -23.1 |
| jctc1-pass.qcir | 80.0 | 60.0 | -20.0 |
| DW-unsat-11-26-1.qcir | 72.9 | 55.5 | -17.3 |
| klieber2017q-086-21-t1.qcir | 18.6 | 9.5 | -9.1 |
| test_5_5_knobby.pg-9.qcir | 26.3 | 18.0 | -8.2 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc4-fail.qcir | 9.9 | 41.3 | +31.4 |
| bt2nd-3x6_10.ig.qcir | 90.8 | 120.0 | +29.2 |
| DWs-unsat-08-17-1.qcir | 91.7 | 120.0 | +28.3 |
| klieber2017q-088-22-eq.qcir | 62.7 | 90.8 | +28.2 |
| jctc14-unrolled-fail.qcir | 92.4 | 120.0 | +27.6 |
| CM-sat-04-01-06-4.qcir | 96.5 | 120.0 | +23.5 |
| amba2f9n.sat.qcir | 53.5 | 76.3 | +22.9 |
| JP-unsat-02-06-3.qcir | 59.4 | 76.6 | +17.2 |
| reachqu_query64_1344.qcir | 17.6 | 33.1 | +15.5 |
| SR-unsat-04-01-08-1.qcir | 58.3 | 70.8 | +12.5 |

## Peak memory

5 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| jctc6-pass.qcir | 64 | 120 | 1.88x |
| bt-3x6_9.ig.qcir | 14 | 20 | 1.42x |
| jctc13-fail.qcir | 17 | 23 | 1.40x |
| CM-sat-04-01-07-3.qcir | 480 | 574 | 1.20x |
| jctc8-pass.qcir | 49 | 56 | 1.14x |

