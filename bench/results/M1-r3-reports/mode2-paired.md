# Paired comparison: B (M1-r3-mode2-s1) against A (baseline-c96-mode2-t60-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=2` | c39005a | 10ff614c6694 | 2026-11-23T02:40:07 |
| B | `-mode=2` | 46874d9 | 006221175f2f | 2026-11-23T20:54:38 |

Order in which the runs started:

- 2026-11-23T02:40:07 `baseline-c96-mode2-t60-s1`
- 2026-11-23T20:54:38 `M1-r3-mode2-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-1.39 s**, 95% bootstrap interval [-3.05, +0.13] (10000 resamples).

Sign test: B wins on 43 instances, loses on 18, ties on 315; two-sided p = 0.0019 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 33 | 0.906 | 10 | 23 |
| all (per instance) | 33 | 0.906 | 10 | 23 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 3 | 0.900 |  |
| DWs | 2 | 0.750 |  |
| Lights | 1 | 1.034 |  |
| chess | 5 | 1.074 |  |
| collector | 1 | 0.996 |  |
| finding | 1 | 0.844 |  |
| hadw | 3 | 0.846 |  |
| jctc | 1 | 0.796 |  |
| lift | 1 | 0.742 |  |
| numeric | 14 | 0.904 |  |
| round | 1 | 0.850 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 1.242 | 1.26 | 1.56 |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 1.149 | 1.04 | 1.20 |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 1.073 | 8.11 | 8.70 |
| DW-unsat-09-23-1.qcir | 1.051 | 20.28 | 21.32 |
| 5.2-2.qcir | 1.037 | 49.98 | 51.80 |
| Lights2_b02056d6.tlsf.qcir | 1.034 | 26.78 | 27.69 |
| 9.3.qcir | 1.027 | 2.93 | 3.01 |
| 9.2.qcir | 1.022 | 23.36 | 23.86 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 1.018 | 4.18 | 4.25 |
| 8.1.qcir | 1.007 | 5.05 | 5.08 |
| 11.1.qcir | 0.997 | 52.26 | 52.12 |
| collector_v17.tlsf.qcir | 0.996 | 7.19 | 7.16 |
| 3.1.qcir | 0.986 | 48.70 | 48.03 |
| 5.2-1.qcir | 0.976 | 5.73 | 5.60 |
| DWs-sat-10-25-1.qcir | 0.948 | 2.92 | 2.77 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DWs-unsat-08-18-1.qcir | 0.594 | 19.96 | 11.86 |
| 3.2.qcir | 0.733 | 1.16 | 0.85 |
| 10.2.qcir | 0.738 | 1.68 | 1.24 |
| lift_gr1+2.tlsf.qcir | 0.742 | 4.86 | 3.61 |
| 1.4.qcir | 0.790 | 7.47 | 5.90 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 77/53/130 | 82.3 | 78/57/135 | 80.9 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 130-130 | 82.3-82.3 |
| B | 135-135 | 80.9-80.9 |

## Instances gained and lost in a majority of seeds

- gained by B (7): `CM-sat-04-01-07-3.qcir`, `JP-unsat-02-06-3.qcir`, `hadw2-8.qcir`, `jctc8-pass.qcir`, `klieber2017q-072-18-t1.qcir`, `klieber2017q-100-25-t1.qcir`, `ltl2dba_beta6.tlsf.qcir`
- lost by B (2): `CM-sat-04-01-06-4.qcir`, `jctc6-pass.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 108.8 | 103.2 | -5.6 | 1 | 1 |
| DW | 7 | 40.5 | 40.1 | -0.4 | 1 | 0 |
| DWs | 13 | 97.2 | 96.7 | -0.4 | 1 | 0 |
| JP | 6 | 120.0 | 108.7 | -11.3 | 1 | 0 |
| Lights | 2 | 73.4 | 73.9 | +0.4 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 97.6 | 97.3 | -0.2 | 1 | 0 |
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
| chess | 40 | 31.1 | 31.0 | -0.1 | 3 | 2 |
| ci | 30 | 88.4 | 88.8 | +0.4 | 3 | 1 |
| collector | 1 | 7.2 | 7.2 | -0.0 | 0 | 0 |
| connect | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 64.2 | 65.6 | +1.4 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 48.4 | 40.9 | -7.6 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 75.9 | 72.1 | -3.8 | 5 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.4 | 83.3 | -0.1 | 1 | 1 |
| klieber | 26 | 43.9 | 37.0 | -6.9 | 9 | 11 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 62.4 | 61.8 | -0.6 | 1 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.8 | 96.8 | -0.1 | 0 | 0 |
| ltl | 5 | 120.0 | 106.9 | -13.1 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 0.8 | 0.7 | -0.0 | 0 | 0 |
| numeric | 26 | 31.8 | 31.6 | -0.2 | 3 | 0 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 57.2 | 54.9 | -2.3 | 1 | 0 |
| robot | 1 | 51.1 | 24.3 | -26.8 | 1 | 0 |
| round | 1 | 3.0 | 2.6 | -0.4 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 77.2 | 75.1 | -2.1 | 4 | 0 |
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
| CM-sat-04-01-07-3.qcir | 120.0 | 2.3 | -117.7 |
| klieber2017q-072-18-t1.qcir | 120.0 | 6.5 | -113.5 |
| klieber2017q-100-25-t1.qcir | 120.0 | 18.1 | -101.9 |
| hadw2-8.qcir | 120.0 | 48.9 | -71.1 |
| JP-unsat-02-06-3.qcir | 120.0 | 52.4 | -67.6 |
| ltl2dba_beta6.tlsf.qcir | 120.0 | 54.4 | -65.6 |
| klieber2017q-112-28-t1.qcir | 49.7 | 16.4 | -33.3 |
| robot_grid6_1.tlsf.qcir | 51.1 | 24.3 | -26.8 |
| klieber2017q-088-22-t1.qcir | 34.2 | 7.7 | -26.5 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc6-pass.qcir | 0.1 | 120.0 | +119.9 |
| CM-sat-04-01-06-4.qcir | 41.7 | 120.0 | +78.3 |
| klieber2017q-066-16-eq.qcir | 15.8 | 50.4 | +34.7 |
| klieber2017q-074-18-t1.qcir | 10.0 | 37.0 | +27.0 |
| klieber2017q-068-17-t1.qcir | 23.4 | 47.5 | +24.1 |
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 1.5 | 20.2 | +18.8 |
| klieber2017q-072-18-eq.qcir | 16.7 | 33.6 | +17.0 |
| klieber2017q-060-15-eq.qcir | 8.2 | 18.4 | +10.2 |
| klieber2017q-078-19-eq.qcir | 28.1 | 37.7 | +9.6 |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 7.6 | 15.3 | +7.7 |

## Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 13 | 18 | 1.42x |
| sc-ungrounded-1x2X2x2_2.qcir | 56 | 77 | 1.36x |
| DWs-unsat-08-17-1.qcir | 182 | 218 | 1.20x |

