# Paired comparison: B (M1-r2-default-s1, M1-r2-default-s2, M1-r2-default-s3) against A (baseline-c96-default-t60-s1, baseline-c96-default-t60-s2, baseline-c96-default-t60-s3)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1, 2, 3].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | c39005a | 10ff614c6694 | 2026-11-23T01:16:03 |
| B | `` | 25216c2 | 30bd8fe6b956 | 2026-11-23T13:40:40 |

Order in which the runs started:

- 2026-11-23T01:16:03 `baseline-c96-default-t60-s1`
- 2026-11-23T01:39:53 `baseline-c96-default-t60-s2`
- 2026-11-23T02:03:45 `baseline-c96-default-t60-s3`
- 2026-11-23T13:40:40 `M1-r2-default-s1`
- 2026-11-23T13:46:42 `M1-r2-default-s2`
- 2026-11-23T13:52:43 `M1-r2-default-s3`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 3 seeds): **+0.24 s**, 95% bootstrap interval [-0.52, +1.05] (10000 resamples).

Sign test: B wins on 32 instances, loses on 21, ties on 323; two-sided p = 0.1690 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 40 | 1.027 | 20 | 20 |
| 2 | 40 | 1.042 | 25 | 14 |
| 3 | 37 | 1.007 | 20 | 17 |
| all (per instance) | 51 | 1.037 | 28 | 23 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| CM | 1 | 1.035 |  |
| DW | 6 | 1.144 | > 1.10 |
| DWs | 1 | 0.965 |  |
| Lights | 1 | 1.126 |  |
| chess | 16 | 1.076 |  |
| collector | 1 | 0.943 |  |
| finding | 1 | 0.981 |  |
| hadw | 3 | 1.133 | > 1.10 |
| jctc | 4 | 1.038 |  |
| lift | 1 | 0.930 |  |
| ltl | 1 | 1.014 |  |
| numeric | 15 | 0.957 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DW-sat-08-23-1.qcir | 1.530 | 2.00 | 3.07 |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | 1.355 | 1.08 | 1.46 |
| DW-unsat-09-22-1.qcir | 1.332 | 15.38 | 19.85 |
| jctc2-pass.qcir | 1.274 | 2.05 | 2.61 |
| 5.2-1.qcir | 1.261 | 20.95 | 26.44 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 1.224 | 8.43 | 10.44 |
| 5.1-1.qcir | 1.212 | 40.74 | 49.21 |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 1.168 | 1.26 | 1.49 |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 1.165 | 6.25 | 7.25 |
| DW-sat-08-22-1.qcir | 1.160 | 2.54 | 2.90 |
| hadw11-12.qcir | 1.153 | 5.14 | 5.95 |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 1.142 | 3.18 | 3.37 |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 1.132 | 4.82 | 5.75 |
| Lights2_0f5381e9.tlsf.qcir | 1.126 | 32.32 | 36.42 |
| hadw9-10.qcir | 1.123 | 1.39 | 1.62 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 3.2.qcir | 0.751 | 1.26 | 0.95 |
| 9.1.qcir | 0.760 | 2.16 | 1.64 |
| 10.2.qcir | 0.847 | 2.07 | 1.83 |
| 1.3.qcir | 0.862 | 8.13 | 7.02 |
| 10.1.qcir | 0.862 | 1.94 | 1.67 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 82/59/141 | 79.3 | 81/59/140 | 79.9 |
| 2 | 86/60/146 | 77.9 | 85/59/144 | 78.3 |
| 3 | 85/58/143 | 79.1 | 83/60/143 | 78.9 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 141-146 | 77.9-79.3 |
| B | 140-144 | 78.3-79.9 |

## Instances gained and lost in a majority of seeds

- gained by B (1): `test_5_5_knobby.pg-9.qcir`
- lost by B (2): `klieber2017q-076-19-eq.qcir`, `klieber2017q-108-27-t1.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 95.1 | 105.6 | +10.5 | 1 | 3 |
| DW | 7 | 31.8 | 32.5 | +0.7 | 0 | 1 |
| DWs | 13 | 117.3 | 117.3 | -0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 79.8 | 92.2 | +12.4 | 0 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.2 | 100.7 | -0.5 | 1 | 0 |
| arbiter | 6 | 84.8 | 84.9 | +0.1 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 82.7 | 79.3 | -3.5 | 2 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 27.3 | 28.0 | +0.7 | 0 | 6 |
| ci | 30 | 100.1 | 100.1 | +0.0 | 0 | 1 |
| collector | 1 | 4.4 | 4.2 | -0.2 | 0 | 0 |
| connect | 7 | 86.9 | 86.8 | -0.2 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 74.7 | 79.3 | +4.6 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 10.3 | 10.2 | -0.2 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.5 | 76.1 | -0.4 | 2 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 75.7 | 75.6 | -0.1 | 0 | 0 |
| klieber | 26 | 49.9 | 52.1 | +2.3 | 14 | 6 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.8 | 60.7 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.6 | 98.8 | +0.2 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.3 | 111.9 | +0.7 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 80.0 | 80.0 | -0.0 | 0 | 0 |
| numeric | 26 | 31.8 | 33.0 | +1.2 | 2 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 88.9 | 87.9 | -1.0 | 0 | 0 |
| robot | 1 | 5.2 | 3.9 | -1.3 | 1 | 0 |
| round | 1 | 2.0 | 1.9 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 59.0 | 57.4 | -1.5 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 47.2 | 44.4 | -2.7 | 6 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| test_5_5_knobby.pg-9.qcir | 90.6 | 41.3 | -49.4 |
| CM-sat-04-01-06-3.qcir | 90.4 | 58.6 | -31.9 |
| klieber2017q-112-28-t1.qcir | 120.0 | 89.8 | -30.2 |
| klieber2017q-084-21-eq.qcir | 120.0 | 92.3 | -27.7 |
| klieber2017q-100-25-t1.qcir | 93.7 | 70.6 | -23.0 |
| bt2nd-3x6_10.ig.qcir | 120.0 | 99.5 | -20.5 |
| bt-2x5_17.ig.qcir | 120.0 | 99.8 | -20.2 |
| klieber2017q-068-17-t1.qcir | 40.2 | 25.9 | -14.2 |
| klieber2017q-078-19-t1.qcir | 61.8 | 48.7 | -13.1 |
| klieber2017q-074-18-t1.qcir | 36.1 | 24.9 | -11.3 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-088-22-t1.qcir | 10.2 | 71.3 | +61.1 |
| klieber2017q-108-27-t1.qcir | 35.4 | 84.4 | +49.1 |
| klieber2017q-076-19-t1.qcir | 29.2 | 71.2 | +42.0 |
| klieber2017q-076-19-eq.qcir | 51.4 | 92.1 | +40.7 |
| CM-sat-04-01-06-4.qcir | 43.8 | 80.4 | +36.6 |
| CM-sat-04-01-07-3.qcir | 84.4 | 120.0 | +35.6 |
| CM-sat-07-01-06-3.qcir | 87.2 | 120.0 | +32.8 |
| 5.2-1.qcir | 31.7 | 57.6 | +25.9 |
| Lights2_b02056d6.tlsf.qcir | 97.9 | 120.0 | +22.1 |
| klieber2017q-078-19-eq.qcir | 48.1 | 68.0 | +19.9 |

## Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| sc-ungrounded-1x3X3x2_1.qcir | 26 | 35 | 1.36x |
| bt-3x6_9.ig.qcir | 15 | 17 | 1.13x |
| sc-ungrounded-2x1X1x2_2.qcir | 47 | 53 | 1.12x |

