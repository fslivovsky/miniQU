# Paired comparison: B (M1-r2-mode2-s1) against A (baseline-c96-mode2-t60-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=2` | c39005a | 10ff614c6694 | 2026-11-23T02:40:07 |
| B | `-mode=2` | 25216c2 | 30bd8fe6b956 | 2026-11-23T14:22:37 |

Order in which the runs started:

- 2026-11-23T02:40:07 `baseline-c96-mode2-t60-s1`
- 2026-11-23T14:22:37 `M1-r2-mode2-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-1.10 s**, 95% bootstrap interval [-2.76, +0.44] (10000 resamples).

Sign test: B wins on 39 instances, loses on 23, ties on 314; two-sided p = 0.0559 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 33 | 0.975 | 16 | 17 |
| all (per instance) | 33 | 0.975 | 16 | 17 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 3 | 1.013 |  |
| DWs | 2 | 0.876 |  |
| Lights | 1 | 1.081 |  |
| chess | 5 | 1.187 | > 1.10 |
| collector | 1 | 0.839 |  |
| finding | 1 | 1.052 |  |
| hadw | 3 | 0.918 |  |
| jctc | 1 | 0.827 |  |
| lift | 1 | 1.040 |  |
| numeric | 14 | 0.930 |  |
| round | 1 | 1.012 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 1.266 | 1.29 | 1.64 |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 1.262 | 8.11 | 10.23 |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 1.180 | 1.26 | 1.49 |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 1.132 | 1.04 | 1.18 |
| 5.2-2.qcir | 1.123 | 49.98 | 56.13 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 1.102 | 4.18 | 4.61 |
| 5.2-1.qcir | 1.097 | 5.73 | 6.29 |
| Lights2_b02056d6.tlsf.qcir | 1.081 | 26.78 | 28.95 |
| DW-unsat-09-22-1.qcir | 1.064 | 21.05 | 22.41 |
| DW-unsat-09-23-1.qcir | 1.055 | 20.28 | 21.40 |
| finding_nemo_1.tlsf.qcir | 1.052 | 48.36 | 50.86 |
| lift_gr1+2.tlsf.qcir | 1.040 | 4.86 | 5.06 |
| 9.2.qcir | 1.039 | 23.36 | 24.27 |
| 9.3.qcir | 1.020 | 2.93 | 2.99 |
| round_robin_arbiter3.tlsf.qcir | 1.012 | 2.96 | 3.00 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 3.2.qcir | 0.748 | 1.16 | 0.87 |
| 10.2.qcir | 0.755 | 1.68 | 1.27 |
| 1.3.qcir | 0.823 | 7.39 | 6.08 |
| 1.4.qcir | 0.825 | 7.47 | 6.16 |
| jctc4-fail.qcir | 0.827 | 2.70 | 2.23 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 77/53/130 | 82.3 | 77/57/134 | 81.2 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 130-130 | 82.3-82.3 |
| B | 134-134 | 81.2-81.2 |

## Instances gained and lost in a majority of seeds

- gained by B (7): `CM-sat-04-01-07-3.qcir`, `hadw2-8.qcir`, `hadw3-7.qcir`, `jctc8-pass.qcir`, `klieber2017q-072-18-t1.qcir`, `klieber2017q-100-25-t1.qcir`, `ltl2dba_beta6.tlsf.qcir`
- lost by B (3): `CM-sat-04-01-06-4.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `jctc6-pass.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 108.8 | 103.2 | -5.6 | 1 | 1 |
| DW | 7 | 40.5 | 40.9 | +0.4 | 0 | 0 |
| DWs | 13 | 97.2 | 96.8 | -0.4 | 1 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 73.4 | 74.5 | +1.1 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 97.6 | 97.1 | -0.4 | 1 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| arbiter | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 92.3 | 91.3 | -1.0 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 31.1 | 33.1 | +2.0 | 2 | 6 |
| ci | 30 | 88.4 | 88.8 | +0.4 | 3 | 1 |
| collector | 1 | 7.2 | 6.0 | -1.2 | 1 | 0 |
| connect | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 64.2 | 65.5 | +1.3 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 48.4 | 50.9 | +2.5 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 75.9 | 69.4 | -6.5 | 4 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.4 | 83.3 | -0.1 | 1 | 1 |
| klieber | 26 | 43.9 | 36.8 | -7.1 | 10 | 11 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 62.4 | 62.5 | +0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.8 | 96.8 | -0.1 | 0 | 0 |
| ltl | 5 | 120.0 | 107.5 | -12.5 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 0.8 | 0.7 | -0.1 | 0 | 0 |
| numeric | 26 | 31.8 | 31.8 | +0.1 | 3 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 57.2 | 55.6 | -1.6 | 1 | 0 |
| robot | 1 | 51.1 | 25.1 | -26.0 | 1 | 0 |
| round | 1 | 3.0 | 3.0 | +0.1 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 77.2 | 74.0 | -3.1 | 4 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 79.6 | 79.0 | -0.6 | 4 | 1 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc8-pass.qcir | 120.0 | 0.2 | -119.8 |
| CM-sat-04-01-07-3.qcir | 120.0 | 2.6 | -117.4 |
| klieber2017q-072-18-t1.qcir | 120.0 | 6.4 | -113.6 |
| klieber2017q-100-25-t1.qcir | 120.0 | 18.0 | -102.0 |
| hadw2-8.qcir | 120.0 | 55.0 | -65.0 |
| hadw3-7.qcir | 120.0 | 55.4 | -64.6 |
| ltl2dba_beta6.tlsf.qcir | 120.0 | 57.5 | -62.5 |
| klieber2017q-112-28-t1.qcir | 49.7 | 16.7 | -33.0 |
| klieber2017q-088-22-t1.qcir | 34.2 | 7.5 | -26.7 |
| robot_grid6_1.tlsf.qcir | 51.1 | 25.1 | -26.0 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc6-pass.qcir | 0.1 | 120.0 | +119.9 |
| CM-sat-04-01-06-4.qcir | 41.7 | 120.0 | +78.3 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 57.7 | 120.0 | +62.3 |
| klieber2017q-066-16-eq.qcir | 15.8 | 49.9 | +34.2 |
| klieber2017q-074-18-t1.qcir | 10.0 | 36.6 | +26.7 |
| klieber2017q-068-17-t1.qcir | 23.4 | 47.5 | +24.1 |
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 1.5 | 19.7 | +18.2 |
| klieber2017q-072-18-eq.qcir | 16.7 | 33.3 | +16.6 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 7.6 | 18.0 | +10.4 |
| klieber2017q-060-15-eq.qcir | 8.2 | 18.2 | +10.0 |

## Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 13 | 18 | 1.39x |
| sc-ungrounded-1x2X2x2_2.qcir | 56 | 77 | 1.36x |
| DWs-unsat-08-17-1.qcir | 182 | 221 | 1.21x |

