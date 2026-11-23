# Paired comparison: B (M1-r3-ccmin3-s1) against A (baseline-c96-ccmin3-t60-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-ccmin-mode=3` | c39005a | 10ff614c6694 | 2026-11-23T02:52:10 |
| B | `-ccmin-mode=3` | 46874d9 | 006221175f2f | 2026-11-23T21:00:38 |

Order in which the runs started:

- 2026-11-23T02:52:10 `baseline-c96-ccmin3-t60-s1`
- 2026-11-23T21:00:38 `M1-r3-ccmin3-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-1.52 s**, 95% bootstrap interval [-3.44, +0.32] (10000 resamples).

Sign test: B wins on 42 instances, loses on 20, ties on 314; two-sided p = 0.0071 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 4 | 0.818 | 0 | 4 |
| all (per instance) | 4 | 0.818 | 0 | 4 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DWs | 1 | 0.909 |  |
| numeric | 3 | 0.790 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DWs-sat-12-28-1.qcir | 0.909 | 2.06 | 1.88 |
| 1.4.qcir | 0.857 | 8.81 | 7.55 |
| 10.2.qcir | 0.787 | 1.72 | 1.35 |
| 3.2.qcir | 0.732 | 1.17 | 0.85 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 3.2.qcir | 0.732 | 1.17 | 0.85 |
| 10.2.qcir | 0.787 | 1.72 | 1.35 |
| 1.4.qcir | 0.857 | 8.81 | 7.55 |
| DWs-sat-12-28-1.qcir | 0.909 | 2.06 | 1.88 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 87/55/142 | 79.0 | 87/60/147 | 77.5 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 142-142 | 79.0-79.0 |
| B | 147-147 | 77.5-77.5 |

## Instances gained and lost in a majority of seeds

- gained by B (9): `CM-sat-04-01-06-3.qcir`, `DW-unsat-10-25-1.qcir`, `klieber2017q-080-20-t1.qcir`, `klieber2017q-082-20-t1.qcir`, `klieber2017q-084-21-t1.qcir`, `klieber2017q-086-21-t1.qcir`, `klieber2017q-088-22-t1.qcir`, `klieber2017q-108-27-t1.qcir`, `test_5_5_domino.pg-15.qcir`
- lost by B (4): `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `klieber2017q-100-25-t1.qcir`, `klieber2017q-112-28-t1.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 89.4 | 104.8 | +15.3 | 1 | 2 |
| DW | 7 | 38.2 | 31.2 | -7.0 | 1 | 2 |
| DWs | 13 | 110.9 | 110.9 | -0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 58.8 | 55.2 | -3.5 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 88.7 | 87.6 | -1.1 | 0 | 0 |
| arbiter | 6 | 84.8 | 83.5 | -1.3 | 2 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 84.5 | 84.1 | -0.3 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 28.8 | 28.7 | -0.1 | 5 | 5 |
| ci | 30 | 100.2 | 100.1 | -0.1 | 1 | 0 |
| collector | 1 | 3.7 | 2.6 | -1.1 | 1 | 0 |
| connect | 7 | 87.0 | 86.9 | -0.1 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 75.4 | 73.3 | -2.0 | 1 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 8.3 | 7.9 | -0.4 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.1 | 75.9 | -0.2 | 2 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 69.5 | 71.2 | +1.7 | 2 | 1 |
| klieber | 26 | 60.9 | 41.2 | -19.6 | 13 | 5 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.8 | 60.6 | -0.2 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.4 | 97.3 | -1.1 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.1 | 109.9 | -0.2 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 33.6 | 34.5 | +0.9 | 5 | 2 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 80.5 | 81.1 | +0.5 | 0 | 1 |
| robot | 1 | 3.3 | 2.6 | -0.8 | 0 | 0 |
| round | 1 | 1.6 | 1.9 | +0.3 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 58.2 | 57.1 | -1.1 | 2 | 1 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 45.5 | 41.7 | -3.8 | 4 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-080-20-t1.qcir | 120.0 | 9.0 | -111.0 |
| klieber2017q-082-20-t1.qcir | 120.0 | 9.6 | -110.4 |
| klieber2017q-088-22-t1.qcir | 120.0 | 12.6 | -107.4 |
| klieber2017q-108-27-t1.qcir | 120.0 | 12.7 | -107.3 |
| CM-sat-04-01-06-3.qcir | 120.0 | 13.3 | -106.7 |
| klieber2017q-084-21-t1.qcir | 120.0 | 14.6 | -105.4 |
| test_5_5_domino.pg-15.qcir | 120.0 | 27.1 | -92.9 |
| DW-unsat-10-25-1.qcir | 120.0 | 58.7 | -61.3 |
| klieber2017q-086-21-t1.qcir | 120.0 | 59.1 | -60.9 |
| klieber2017q-078-19-t1.qcir | 58.2 | 1.4 | -56.8 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-4.qcir | 8.2 | 120.0 | +111.8 |
| CM-sat-04-01-07-3.qcir | 17.9 | 120.0 | +102.1 |
| klieber2017q-112-28-t1.qcir | 32.6 | 120.0 | +87.4 |
| klieber2017q-100-25-t1.qcir | 32.9 | 120.0 | +87.1 |
| jctc10-fail.qcir | 24.6 | 55.6 | +31.0 |
| 5.2-1.qcir | 12.8 | 42.1 | +29.3 |
| klieber2017q-076-19-t1.qcir | 3.7 | 29.7 | +25.9 |
| klieber2017q-076-19-eq.qcir | 35.2 | 53.3 | +18.1 |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 6.4 | 24.0 | +17.6 |
| 3.1.qcir | 33.8 | 51.4 | +17.6 |

## Peak memory

3 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| jctc10-fail.qcir | 72 | 149 | 2.08x |
| sc-ungrounded-2x1X1x2_2.qcir | 26 | 29 | 1.14x |
| hadw5-7.qcir | 32 | 36 | 1.11x |

