# Paired comparison: B (M1-r1-mode2-s1) against A (baseline-c96-mode2-t60-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-mode=2` | c39005a | 10ff614c6694 | 2026-11-23T02:40:07 |
| B | `-mode=2` | 00eb7a4 | a48a1a946f47 | 2026-11-23T02:34:06 |

Order in which the runs started:

- 2026-11-23T02:34:06 `M1-r1-mode2-s1`
- 2026-11-23T02:40:07 `baseline-c96-mode2-t60-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-0.92 s**, 95% bootstrap interval [-2.59, +0.63] (10000 resamples).

Sign test: B wins on 29 instances, loses on 27, ties on 320; two-sided p = 0.8939 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 33 | 1.026 | 22 | 11 |
| all (per instance) | 33 | 1.026 | 22 | 11 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DW | 3 | 1.181 | > 1.10 |
| DWs | 2 | 1.060 |  |
| Lights | 1 | 1.179 |  |
| chess | 5 | 1.126 | > 1.10 |
| collector | 1 | 1.077 |  |
| finding | 1 | 1.074 |  |
| hadw | 3 | 0.952 |  |
| jctc | 1 | 0.919 |  |
| lift | 1 | 0.887 |  |
| numeric | 14 | 0.988 |  |
| round | 1 | 0.855 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 1.315 | 8.11 | 10.66 |
| DW-unsat-09-22-1.qcir | 1.259 | 21.05 | 26.50 |
| DW-unsat-09-23-1.qcir | 1.211 | 20.28 | 24.57 |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 1.196 | 1.26 | 1.50 |
| 5.2-2.qcir | 1.180 | 49.98 | 58.96 |
| Lights2_b02056d6.tlsf.qcir | 1.179 | 26.78 | 31.57 |
| DWs-sat-10-25-1.qcir | 1.102 | 2.92 | 3.22 |
| 5.2-1.qcir | 1.087 | 5.73 | 6.24 |
| 9.2.qcir | 1.083 | 23.36 | 25.29 |
| 9.3.qcir | 1.081 | 2.93 | 3.17 |
| DW-sat-09-26-1.qcir | 1.080 | 1.03 | 1.11 |
| collector_v17.tlsf.qcir | 1.077 | 7.19 | 7.74 |
| finding_nemo_1.tlsf.qcir | 1.074 | 48.36 | 51.96 |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 1.069 | 1.04 | 1.11 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 1.067 | 4.18 | 4.46 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 10.2.qcir | 0.796 | 1.68 | 1.33 |
| 3.2.qcir | 0.816 | 1.16 | 0.95 |
| round_robin_arbiter3.tlsf.qcir | 0.855 | 2.96 | 2.53 |
| hadw11-12.qcir | 0.862 | 14.60 | 12.59 |
| 1.4.qcir | 0.882 | 7.47 | 6.59 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 77/53/130 | 82.3 | 76/58/134 | 81.3 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 130-130 | 82.3-82.3 |
| B | 134-134 | 81.3-81.3 |

## Instances gained and lost in a majority of seeds

- gained by B (7): `CM-sat-04-01-07-3.qcir`, `JP-unsat-02-06-3.qcir`, `hadw2-8.qcir`, `hadw3-7.qcir`, `jctc8-pass.qcir`, `klieber2017q-072-18-t1.qcir`, `klieber2017q-100-25-t1.qcir`
- lost by B (3): `CM-sat-04-01-06-4.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `jctc6-pass.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 108.8 | 103.2 | -5.6 | 1 | 1 |
| DW | 7 | 40.5 | 42.0 | +1.5 | 0 | 2 |
| DWs | 13 | 97.2 | 98.0 | +0.9 | 0 | 1 |
| JP | 6 | 120.0 | 108.7 | -11.3 | 1 | 0 |
| Lights | 2 | 73.4 | 75.8 | +2.4 | 0 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 97.6 | 97.5 | -0.1 | 0 | 0 |
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
| bt | 12 | 92.3 | 91.4 | -1.0 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 31.1 | 33.0 | +1.9 | 2 | 6 |
| ci | 30 | 88.4 | 88.8 | +0.4 | 2 | 1 |
| collector | 1 | 7.2 | 7.8 | +0.6 | 0 | 0 |
| connect | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 64.2 | 65.8 | +1.5 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 48.4 | 52.0 | +3.6 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 75.9 | 69.3 | -6.7 | 4 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 83.4 | 83.4 | -0.0 | 1 | 1 |
| klieber | 26 | 43.9 | 37.6 | -6.3 | 9 | 11 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 62.4 | 62.2 | -0.3 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.8 | 96.8 | -0.0 | 0 | 0 |
| ltl | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 0.8 | 0.7 | -0.1 | 0 | 0 |
| numeric | 26 | 31.8 | 32.3 | +0.5 | 0 | 1 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 57.2 | 57.5 | +0.3 | 0 | 0 |
| robot | 1 | 51.1 | 24.2 | -26.9 | 1 | 0 |
| round | 1 | 3.0 | 2.6 | -0.4 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 77.2 | 75.2 | -2.0 | 3 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 79.6 | 79.0 | -0.5 | 4 | 1 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc8-pass.qcir | 120.0 | 0.2 | -119.8 |
| CM-sat-04-01-07-3.qcir | 120.0 | 2.6 | -117.4 |
| klieber2017q-072-18-t1.qcir | 120.0 | 6.7 | -113.3 |
| klieber2017q-100-25-t1.qcir | 120.0 | 19.2 | -100.8 |
| hadw3-7.qcir | 120.0 | 48.3 | -71.7 |
| JP-unsat-02-06-3.qcir | 120.0 | 52.1 | -67.9 |
| hadw2-8.qcir | 120.0 | 58.6 | -61.4 |
| klieber2017q-112-28-t1.qcir | 49.7 | 17.5 | -32.2 |
| robot_grid6_1.tlsf.qcir | 51.1 | 24.2 | -26.9 |
| klieber2017q-088-22-t1.qcir | 34.2 | 8.0 | -26.2 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc6-pass.qcir | 0.1 | 120.0 | +119.9 |
| CM-sat-04-01-06-4.qcir | 41.7 | 120.0 | +78.3 |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 57.7 | 120.0 | +62.3 |
| klieber2017q-066-16-eq.qcir | 15.8 | 51.6 | +35.8 |
| klieber2017q-074-18-t1.qcir | 10.0 | 38.1 | +28.2 |
| klieber2017q-068-17-t1.qcir | 23.4 | 49.5 | +26.2 |
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 1.5 | 21.2 | +19.8 |
| klieber2017q-072-18-eq.qcir | 16.7 | 34.4 | +17.7 |
| klieber2017q-078-19-eq.qcir | 28.1 | 39.4 | +11.3 |
| DWs-unsat-08-17-1.qcir | 40.0 | 50.9 | +10.9 |

## Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir | 13 | 19 | 1.53x |
| sc-ungrounded-1x2X2x2_2.qcir | 56 | 78 | 1.39x |
| DWs-unsat-08-17-1.qcir | 182 | 222 | 1.22x |

