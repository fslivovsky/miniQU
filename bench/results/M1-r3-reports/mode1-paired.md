# Paired comparison: B (M1-r3-mode1-s1) against A (baseline-c96-mode1-t60-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=1` | c39005a | 10ff614c6694 | 2026-11-23T02:27:56 |
| B | `-mode=1` | 46874d9 | 006221175f2f | 2026-11-23T20:48:28 |

Order in which the runs started:

- 2026-11-23T02:27:56 `baseline-c96-mode1-t60-s1`
- 2026-11-23T20:48:28 `M1-r3-mode1-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **+0.20 s**, 95% bootstrap interval [-1.19, +1.59] (10000 resamples).

Sign test: B wins on 20 instances, loses on 18, ties on 338; two-sided p = 0.8714 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 36 | 0.990 | 21 | 15 |
| all (per instance) | 36 | 0.990 | 21 | 15 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 5 | 0.916 |  |
| chess | 11 | 1.044 |  |
| collector | 1 | 0.969 |  |
| hadw | 2 | 1.188 |  |
| lift | 1 | 0.886 |  |
| ltl | 1 | 1.010 |  |
| numeric | 14 | 0.967 |  |
| round | 1 | 0.895 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| hadw10-11.qcir | 1.300 | 1.45 | 1.89 |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 1.215 | 15.68 | 19.05 |
| 5.1-1.qcir | 1.196 | 49.95 | 59.74 |
| 4.1.qcir | 1.171 | 7.24 | 8.48 |
| 5.2-1.qcir | 1.118 | 28.50 | 31.87 |
| 9.2.qcir | 1.103 | 19.19 | 21.16 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 1.089 | 10.41 | 11.34 |
| 11.1.qcir | 1.087 | 32.82 | 35.69 |
| hadw11-12.qcir | 1.086 | 8.53 | 9.26 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 1.084 | 2.12 | 2.29 |
| DW-sat-08-23-1.qcir | 1.080 | 1.70 | 1.83 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 1.079 | 18.27 | 19.72 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 1.076 | 14.63 | 15.73 |
| 8.1.qcir | 1.073 | 3.98 | 4.27 |
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | 1.071 | 36.74 | 39.36 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 10.2.qcir | 0.749 | 1.64 | 1.23 |
| DW-unsat-09-22-1.qcir | 0.753 | 12.10 | 9.11 |
| 3.2.qcir | 0.753 | 1.16 | 0.87 |
| 9.1.qcir | 0.773 | 2.16 | 1.67 |
| 1.3.qcir | 0.832 | 7.78 | 6.47 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 72/44/116 | 85.9 | 72/43/115 | 86.1 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 116-116 | 85.9-85.9 |
| B | 115-115 | 86.1-86.1 |

## Instances gained and lost in a majority of seeds

- gained by B (4): `CM-sat-04-01-06-3.qcir`, `Lights2_b02056d6.tlsf.qcir`, `jctc8-pass.qcir`, `reachqu_query64_1344.qcir`
- lost by B (5): `Lights2_0f5381e9.tlsf.qcir`, `hadw6-8.qcir`, `klieber2017q-072-18-eq.qcir`, `reachqu_query60_1344.qcir`, `test_5_5_elly.pg-9.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 120.0 | 103.1 | -16.9 | 1 | 0 |
| DW | 7 | 40.2 | 39.7 | -0.5 | 1 | 0 |
| DWs | 13 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 89.7 | 87.6 | -2.1 | 1 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.4 | 101.7 | +0.3 | 0 | 0 |
| arbiter | 6 | 85.0 | 85.0 | -0.0 | 1 | 1 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 92.5 | 93.7 | +1.3 | 0 | 1 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 29.3 | 29.4 | +0.1 | 1 | 3 |
| ci | 30 | 100.1 | 100.1 | -0.1 | 1 | 0 |
| collector | 1 | 3.5 | 3.4 | -0.1 | 0 | 0 |
| connect | 7 | 89.1 | 89.1 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 71.2 | 72.2 | +1.0 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 11.7 | 9.3 | -2.5 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 69.2 | 72.2 | +3.0 | 1 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.9 | 77.1 | -6.8 | 1 | 0 |
| klieber | 26 | 112.1 | 116.5 | +4.4 | 0 | 2 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.2 | 61.0 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.3 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 97.8 | 97.8 | +0.0 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.3 | 110.8 | +0.5 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 31.3 | 32.0 | +0.7 | 2 | 4 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 83.3 | 91.7 | +8.4 | 1 | 1 |
| robot | 1 | 4.5 | 3.8 | -0.7 | 0 | 0 |
| round | 1 | 1.5 | 1.4 | -0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 58.2 | 56.7 | -1.6 | 2 | 0 |
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
| jctc8-pass.qcir | 120.0 | 31.8 | -88.2 |
| reachqu_query64_1344.qcir | 120.0 | 35.1 | -84.9 |
| Lights2_b02056d6.tlsf.qcir | 120.0 | 55.3 | -64.7 |
| sc-ungrounded-2x2X2x2_1.qcir | 26.4 | 14.5 | -11.8 |
| test_5_5_Z.pg-7.qcir | 14.7 | 6.4 | -8.3 |
| test_5_5_snaky.pg-7.qcir | 15.7 | 7.5 | -8.2 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 40.8 | 32.8 | -8.0 |
| test_5_5_domino.pg-11.qcir | 10.7 | 4.2 | -6.5 |
| hadw4-7.qcir | 59.9 | 55.1 | -4.8 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| reachqu_query60_1344.qcir | 9.8 | 120.0 | +110.2 |
| klieber2017q-072-18-eq.qcir | 20.7 | 120.0 | +99.3 |
| test_5_5_elly.pg-9.qcir | 46.9 | 120.0 | +73.1 |
| hadw6-8.qcir | 51.1 | 120.0 | +68.9 |
| Lights2_0f5381e9.tlsf.qcir | 59.5 | 120.0 | +60.5 |
| klieber2017q-060-15-eq.qcir | 13.3 | 29.2 | +15.9 |
| bt2nd-2x5_10.ig.qcir | 28.0 | 42.4 | +14.5 |
| 5.1-1.qcir | 50.0 | 59.8 | +9.8 |
| test_5_5_elly.pg-7.qcir | 1.6 | 10.7 | +9.1 |
| test_5_5_L.pg-7.qcir | 1.3 | 7.2 | +5.9 |

## Peak memory

0 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

