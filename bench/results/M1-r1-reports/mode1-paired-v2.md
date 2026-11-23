# Paired comparison: B (M1-r1-mode1-s1) against A (baseline-c96-mode1-t60-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=1` | c39005a | 10ff614c6694 | 2026-11-23T02:27:56 |
| B | `-mode=1` | 00eb7a4 | a48a1a946f47 | 2026-11-23T02:21:44 |

Order in which the runs started:

- 2026-11-23T02:21:44 `M1-r1-mode1-s1`
- 2026-11-23T02:27:56 `baseline-c96-mode1-t60-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **+0.44 s**, 95% bootstrap interval [-0.92, +1.83] (10000 resamples).

Sign test: B wins on 14 instances, loses on 31, ties on 331; two-sided p = 0.0161 (margin max(1 s, 10% of the smaller score)).

**Verdict: B is worse than A.**

B is not worse than A: **no**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 35 | 1.140 | 27 | 8 |
| all (per instance) | 35 | 1.140 | 27 | 8 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 5 | 1.351 | > 1.10 |
| chess | 11 | 1.220 | > 1.10 |
| collector | 1 | 1.066 |  |
| hadw | 2 | 1.362 |  |
| lift | 1 | 0.985 |  |
| ltl | 1 | 1.140 |  |
| numeric | 13 | 1.009 |  |
| round | 1 | 0.975 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DW-unsat-09-22-1.qcir | 1.765 | 12.10 | 21.34 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 1.748 | 10.41 | 18.20 |
| DW-sat-08-23-1.qcir | 1.684 | 1.70 | 2.86 |
| hadw10-11.qcir | 1.579 | 1.45 | 2.29 |
| DW-unsat-09-23-1.qcir | 1.315 | 17.42 | 22.90 |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | 1.296 | 1.06 | 1.37 |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 1.264 | 2.60 | 3.29 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 1.252 | 14.63 | 18.32 |
| 5.2-1.qcir | 1.242 | 28.50 | 35.39 |
| 4.1.qcir | 1.178 | 7.24 | 8.53 |
| hadw11-12.qcir | 1.175 | 8.53 | 10.02 |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 1.169 | 2.12 | 2.47 |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 1.168 | 1.33 | 1.55 |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 1.156 | 15.68 | 18.13 |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 1.147 | 18.27 | 20.95 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 10.2.qcir | 0.806 | 1.64 | 1.32 |
| 3.2.qcir | 0.815 | 1.16 | 0.94 |
| 9.1.qcir | 0.867 | 2.16 | 1.88 |
| 1.3.qcir | 0.910 | 7.78 | 7.08 |
| 10.1.qcir | 0.914 | 2.17 | 1.99 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 72/44/116 | 85.9 | 70/45/115 | 86.3 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 116-116 | 85.9-85.9 |
| B | 115-115 | 86.3-86.3 |

## Instances gained and lost in a majority of seeds

- gained by B (4): `CM-sat-04-01-06-3.qcir`, `jctc14-unrolled-fail.qcir`, `jctc8-pass.qcir`, `reachqu_query64_1344.qcir`
- lost by B (5): `5.1-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `klieber2017q-072-18-eq.qcir`, `reachqu_query60_1344.qcir`, `test_5_5_elly.pg-9.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 120.0 | 103.1 | -16.9 | 1 | 0 |
| DW | 7 | 40.2 | 42.6 | +2.4 | 0 | 3 |
| DWs | 13 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 89.7 | 120.0 | +30.3 | 0 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 101.4 | 101.6 | +0.1 | 0 | 0 |
| arbiter | 6 | 85.0 | 85.2 | +0.2 | 0 | 1 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 92.5 | 93.8 | +1.3 | 0 | 1 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 29.3 | 30.2 | +0.9 | 0 | 8 |
| ci | 30 | 100.1 | 100.1 | -0.1 | 1 | 0 |
| collector | 1 | 3.5 | 3.7 | +0.2 | 0 | 0 |
| connect | 7 | 89.1 | 89.2 | +0.1 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 71.2 | 72.3 | +1.1 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 11.7 | 13.5 | +1.8 | 0 | 1 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 69.2 | 69.4 | +0.3 | 1 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.9 | 72.5 | -11.4 | 2 | 1 |
| klieber | 26 | 112.1 | 116.5 | +4.5 | 0 | 2 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 61.2 | 61.1 | -0.0 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.3 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 97.8 | 98.0 | +0.3 | 0 | 1 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.3 | 110.8 | +0.6 | 0 | 1 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 31.3 | 34.7 | +3.4 | 0 | 6 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 83.3 | 92.7 | +9.4 | 1 | 1 |
| robot | 1 | 4.5 | 4.0 | -0.5 | 0 | 0 |
| round | 1 | 1.5 | 1.5 | -0.0 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 58.2 | 57.3 | -0.9 | 2 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 68.6 | 70.8 | +2.2 | 6 | 3 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | 120.0 | 1.9 | -118.1 |
| jctc8-pass.qcir | 120.0 | 31.5 | -88.5 |
| reachqu_query64_1344.qcir | 120.0 | 38.1 | -81.9 |
| jctc14-unrolled-fail.qcir | 120.0 | 59.7 | -60.3 |
| test_5_5_snaky.pg-7.qcir | 15.7 | 7.5 | -8.2 |
| test_5_5_Z.pg-7.qcir | 14.7 | 6.5 | -8.1 |
| test_5_5_domino.pg-11.qcir | 10.7 | 4.2 | -6.4 |
| sc-ungrounded-2x2X2x2_1.qcir | 26.4 | 20.1 | -6.3 |
| test_5_5_knobby.pg-7.qcir | 9.5 | 7.2 | -2.3 |
| test_5_5_tic.pg-9.qcir | 12.5 | 10.3 | -2.2 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| reachqu_query60_1344.qcir | 9.8 | 120.0 | +110.2 |
| klieber2017q-072-18-eq.qcir | 20.7 | 120.0 | +99.3 |
| test_5_5_elly.pg-9.qcir | 46.9 | 120.0 | +73.1 |
| 5.1-1.qcir | 50.0 | 120.0 | +70.0 |
| Lights2_0f5381e9.tlsf.qcir | 59.5 | 120.0 | +60.5 |
| klieber2017q-060-15-eq.qcir | 13.3 | 30.2 | +16.9 |
| bt2nd-2x5_10.ig.qcir | 28.0 | 43.2 | +15.3 |
| DW-unsat-09-22-1.qcir | 12.1 | 21.3 | +9.2 |
| test_5_5_elly.pg-7.qcir | 1.6 | 10.7 | +9.1 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 10.4 | 18.2 | +7.8 |

## Peak memory

2 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| hadw6-8.qcir | 108 | 126 | 1.17x |
| hadw5-7.qcir | 27 | 30 | 1.11x |

