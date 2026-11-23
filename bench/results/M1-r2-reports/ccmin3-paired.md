# Paired comparison: B (M1-r2-ccmin3-s1) against A (baseline-c96-ccmin3-t60-s1)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 48, mem_gb 8, cores 48-95, timeout 60.0 s, 376 instances compared, seeds [1].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-ccmin-mode=3` | c39005a | 10ff614c6694 | 2026-11-23T02:52:10 |
| B | `-ccmin-mode=3` | 25216c2 | 30bd8fe6b956 | 2026-11-23T14:28:38 |

Order in which the runs started:

- 2026-11-23T02:52:10 `baseline-c96-ccmin3-t60-s1`
- 2026-11-23T14:28:38 `M1-r2-ccmin3-s1`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **-1.32 s**, 95% bootstrap interval [-3.27, +0.56] (10000 resamples).

Sign test: B wins on 43 instances, loses on 23, ties on 310; two-sided p = 0.0187 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 1 | 4 | 0.834 | 0 | 4 |
| all (per instance) | 4 | 0.834 | 0 | 4 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| DWs | 1 | 0.906 |  |
| numeric | 3 | 0.811 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| DWs-sat-12-28-1.qcir | 0.906 | 2.06 | 1.87 |
| 1.4.qcir | 0.890 | 8.81 | 7.84 |
| 10.2.qcir | 0.803 | 1.72 | 1.38 |
| 3.2.qcir | 0.747 | 1.17 | 0.87 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 3.2.qcir | 0.747 | 1.17 | 0.87 |
| 10.2.qcir | 0.803 | 1.72 | 1.38 |
| 1.4.qcir | 0.890 | 8.81 | 7.84 |
| DWs-sat-12-28-1.qcir | 0.906 | 2.06 | 1.87 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 1 | 87/55/142 | 79.0 | 85/61/146 | 77.7 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 142-142 | 79.0-79.0 |
| B | 146-146 | 77.7-77.7 |

## Instances gained and lost in a majority of seeds

- gained by B (9): `CM-sat-04-01-06-3.qcir`, `DW-unsat-10-25-1.qcir`, `klieber2017q-080-20-t1.qcir`, `klieber2017q-082-20-t1.qcir`, `klieber2017q-084-21-t1.qcir`, `klieber2017q-086-21-t1.qcir`, `klieber2017q-088-22-t1.qcir`, `klieber2017q-108-27-t1.qcir`, `test_5_5_domino.pg-15.qcir`
- lost by B (5): `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `klieber2017q-112-28-t1.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 89.4 | 104.8 | +15.4 | 1 | 2 |
| DW | 7 | 38.2 | 31.0 | -7.2 | 1 | 2 |
| DWs | 13 | 110.9 | 110.9 | -0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 58.8 | 120.0 | +61.2 | 0 | 2 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 88.7 | 87.3 | -1.4 | 1 | 0 |
| arbiter | 6 | 84.8 | 83.8 | -1.0 | 2 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 84.5 | 84.1 | -0.3 | 1 | 0 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 28.8 | 29.1 | +0.3 | 4 | 6 |
| ci | 30 | 100.2 | 100.1 | -0.1 | 1 | 0 |
| collector | 1 | 3.7 | 2.6 | -1.1 | 1 | 0 |
| connect | 7 | 87.0 | 86.9 | -0.1 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 75.4 | 73.1 | -2.3 | 1 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 8.3 | 8.0 | -0.3 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 76.1 | 76.0 | -0.0 | 2 | 1 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 69.5 | 71.0 | +1.5 | 2 | 1 |
| klieber | 26 | 60.9 | 38.5 | -22.3 | 14 | 5 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.8 | 60.7 | -0.2 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 98.4 | 97.4 | -1.0 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.1 | 109.9 | -0.2 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 33.6 | 34.7 | +1.1 | 5 | 2 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 80.5 | 81.1 | +0.5 | 0 | 1 |
| robot | 1 | 3.3 | 2.5 | -0.8 | 0 | 0 |
| round | 1 | 1.6 | 2.0 | +0.4 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 58.2 | 56.9 | -1.3 | 2 | 1 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 45.5 | 41.6 | -3.9 | 4 | 0 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-080-20-t1.qcir | 120.0 | 8.8 | -111.2 |
| klieber2017q-082-20-t1.qcir | 120.0 | 9.5 | -110.5 |
| klieber2017q-088-22-t1.qcir | 120.0 | 12.5 | -107.5 |
| klieber2017q-108-27-t1.qcir | 120.0 | 12.5 | -107.5 |
| CM-sat-04-01-06-3.qcir | 120.0 | 13.6 | -106.4 |
| klieber2017q-084-21-t1.qcir | 120.0 | 14.5 | -105.5 |
| test_5_5_domino.pg-15.qcir | 120.0 | 27.1 | -92.9 |
| DW-unsat-10-25-1.qcir | 120.0 | 51.3 | -68.7 |
| klieber2017q-086-21-t1.qcir | 120.0 | 57.7 | -62.3 |
| klieber2017q-078-19-t1.qcir | 58.2 | 1.4 | -56.8 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| CM-sat-04-01-06-4.qcir | 8.2 | 120.0 | +111.8 |
| CM-sat-04-01-07-3.qcir | 17.9 | 120.0 | +102.1 |
| klieber2017q-112-28-t1.qcir | 32.6 | 120.0 | +87.4 |
| Lights2_b02056d6.tlsf.qcir | 58.4 | 120.0 | +61.6 |
| Lights2_0f5381e9.tlsf.qcir | 59.2 | 120.0 | +60.8 |
| 5.2-1.qcir | 12.8 | 45.7 | +32.9 |
| jctc10-fail.qcir | 24.6 | 52.4 | +27.8 |
| klieber2017q-076-19-t1.qcir | 3.7 | 29.6 | +25.8 |
| klieber2017q-100-25-t1.qcir | 32.9 | 56.7 | +23.8 |
| 3.1.qcir | 33.8 | 51.9 | +18.2 |

## Peak memory

4 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| jctc10-fail.qcir | 72 | 154 | 2.14x |
| sc-ungrounded-2x1X1x2_2.qcir | 26 | 30 | 1.18x |
| hadw5-7.qcir | 32 | 37 | 1.14x |
| reachqu_query64_1344.qcir | 21 | 23 | 1.11x |

