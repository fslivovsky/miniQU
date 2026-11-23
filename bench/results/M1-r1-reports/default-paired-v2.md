# Paired comparison: B (M1-r1-default-s1, M1-r1-default-s2, M1-r1-default-s3) against A (baseline-c96-default-t60-s1, baseline-c96-default-t60-s2, baseline-c96-default-t60-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | c39005a | 10ff614c6694 | 2026-11-23T01:16:03 |
| B | `` | 00eb7a4 | a48a1a946f47 | 2026-11-23T01:09:59 |

Order in which the runs started:

- 2026-11-23T01:09:59 `M1-r1-default-s1`
- 2026-11-23T01:16:03 `baseline-c96-default-t60-s1`
- 2026-11-23T01:33:52 `M1-r1-default-s2`
- 2026-11-23T01:39:53 `baseline-c96-default-t60-s2`
- 2026-11-23T01:57:44 `M1-r1-default-s3`
- 2026-11-23T02:03:45 `baseline-c96-default-t60-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **+0.58 s**, 95% bootstrap interval [-0.20, +1.42] (10000 resamples).

Sign test: B wins on 27 instances, loses on 28, ties on 321; two-sided p = 1.0000 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 39 | 1.133 | 30 | 9 |
| 2 | 39 | 1.125 | 31 | 8 |
| 3 | 37 | 1.058 | 29 | 8 |
| all (per instance) | 51 | 1.119 | 43 | 8 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 1 | 1.209 |  |
| DW | 6 | 1.279 | > 1.10 |
| DWs | 1 | 1.162 |  |
| Lights | 1 | 1.077 |  |
| chess | 16 | 1.138 | > 1.10 |
| collector | 1 | 1.029 |  |
| finding | 1 | 1.020 |  |
| hadw | 3 | 1.166 | > 1.10 |
| jctc | 4 | 1.293 | > 1.10 |
| lift | 1 | 1.005 |  |
| ltl | 1 | 1.068 |  |
| numeric | 15 | 1.013 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| jctc2-pass.qcir | 2.320 | 2.05 | 4.76 |
| DW-unsat-09-22-1.qcir | 1.682 | 15.38 | 25.19 |
| DW-sat-08-23-1.qcir | 1.484 | 2.00 | 2.96 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 1.422 | 6.25 | 8.61 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 1.338 | 8.43 | 11.15 |
| DW-unsat-09-23-1.qcir | 1.298 | 26.02 | 34.71 |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 1.264 | 4.82 | 6.03 |
| 5.1-1.qcir | 1.248 | 40.74 | 50.72 |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 1.246 | 3.18 | 3.89 |
| 5.2-1.qcir | 1.241 | 20.95 | 26.04 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 1.227 | 3.78 | 4.58 |
| CM-sat-04-01-06-4.qcir | 1.209 | 1.10 | 1.33 |
| hadw10-11.qcir | 1.202 | 2.64 | 3.28 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 1.190 | 1.26 | 1.51 |
| hadw11-12.qcir | 1.181 | 5.14 | 6.10 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 0.806 | 1.01 | 0.82 |
| 3.2.qcir | 0.817 | 1.26 | 1.03 |
| 9.1.qcir | 0.844 | 2.16 | 1.82 |
| 10.1.qcir | 0.882 | 1.94 | 1.71 |
| 10.2.qcir | 0.888 | 2.07 | 1.93 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 82/59/141 | 79.3 | 81/57/138 | 80.5 |
| 2 | 86/60/146 | 77.9 | 85/58/143 | 78.6 |
| 3 | 85/58/143 | 79.1 | 83/60/143 | 79.0 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 141-146 | 77.9-79.3 |
| B | 138-143 | 78.6-80.5 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `test_5_5_knobby.pg-9.qcir`
- lost by B (3): `DW-unsat-10-25-1.qcir`, `klieber2017q-076-19-eq.qcir`, `klieber2017q-108-27-t1.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 95.1 | 105.7 | +10.5 | 1 | 3 |
| DW | 7 | 31.8 | 41.5 | +9.6 | 0 | 3 |
| DWs | 13 | 117.3 | 117.4 | +0.1 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 79.8 | 91.6 | +11.9 | 0 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.2 | 100.8 | -0.4 | 0 | 0 |
| arbiter | 6 | 84.8 | 84.9 | +0.1 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 82.7 | 81.1 | -1.6 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 27.3 | 28.0 | +0.7 | 0 | 9 |
| ci | 30 | 100.1 | 100.1 | +0.0 | 0 | 1 |
| collector | 1 | 4.4 | 4.6 | +0.2 | 0 | 0 |
| connect | 7 | 86.9 | 86.8 | -0.1 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 74.7 | 79.4 | +4.7 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 10.3 | 10.6 | +0.2 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.5 | 76.2 | -0.3 | 2 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 75.7 | 75.8 | +0.1 | 0 | 0 |
| klieber | 26 | 49.9 | 53.1 | +3.2 | 14 | 6 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.8 | 60.8 | +0.0 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.6 | 99.1 | +0.5 | 0 | 1 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.3 | 112.0 | +0.8 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 80.0 | -0.0 | 0 | 0 |
| numeric | 26 | 31.8 | 33.3 | +1.5 | 0 | 2 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 88.9 | 88.1 | -0.8 | 0 | 0 |
| robot | 1 | 5.2 | 4.1 | -1.1 | 1 | 0 |
| round | 1 | 2.0 | 2.0 | -0.0 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 59.0 | 57.7 | -1.2 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 47.2 | 44.5 | -2.7 | 5 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| test_5_5_knobby.pg-9.qcir | 90.6 | 41.3 | -49.3 |
| CM-sat-04-01-06-3.qcir | 90.4 | 59.1 | -31.3 |
| klieber2017q-112-28-t1.qcir | 120.0 | 90.0 | -30.0 |
| klieber2017q-084-21-eq.qcir | 120.0 | 92.5 | -27.5 |
| klieber2017q-100-25-t1.qcir | 93.7 | 72.2 | -21.5 |
| bt2nd-3x6_10.ig.qcir | 120.0 | 100.0 | -20.0 |
| klieber2017q-068-17-t1.qcir | 40.2 | 27.0 | -13.2 |
| klieber2017q-078-19-t1.qcir | 61.8 | 50.5 | -11.2 |
| klieber2017q-074-18-t1.qcir | 36.1 | 25.8 | -10.4 |
| klieber2017q-080-20-t1.qcir | 31.8 | 23.1 | -8.7 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-088-22-t1.qcir | 10.2 | 72.9 | +62.8 |
| klieber2017q-108-27-t1.qcir | 35.4 | 84.6 | +49.2 |
| DW-unsat-10-25-1.qcir | 52.2 | 99.5 | +47.3 |
| klieber2017q-076-19-t1.qcir | 29.2 | 72.5 | +43.3 |
| klieber2017q-076-19-eq.qcir | 51.4 | 92.4 | +41.0 |
| CM-sat-04-01-06-4.qcir | 43.8 | 80.5 | +36.7 |
| CM-sat-04-01-07-3.qcir | 84.4 | 120.0 | +35.6 |
| CM-sat-07-01-06-3.qcir | 87.2 | 120.0 | +32.8 |
| 5.2-1.qcir | 31.7 | 57.4 | +25.6 |
| Lights2_b02056d6.tlsf.qcir | 97.9 | 120.0 | +22.1 |

## Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| sc-ungrounded-1x3X3x2_1.qcir | 26 | 37 | 1.44x |
| bt-3x6_9.ig.qcir | 15 | 20 | 1.31x |
| sc-ungrounded-2x1X1x2_2.qcir | 47 | 55 | 1.16x |

