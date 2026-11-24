# Paired comparison: B (M2-screen-ccmin3-dl-s4) against A (M2-screen-ref-dl-s4)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [4].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `-dl` | 49df19e | 0c2f34956a22 | 2026-11-24T11:54:42 |
| B | `-dl --ccminmode=3` | 49df19e+dirty | 0c2f34956a22 | 2026-11-24T12:16:31 |

Order in which the runs started:

- 2026-11-24T11:54:42 `M2-screen-ref-dl-s4`
- 2026-11-24T12:16:31 `M2-screen-ccmin3-dl-s4`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **+0.40 s**, 95% bootstrap interval [-1.21, +2.10] (10000 resamples).

Sign test: B wins on 50 instances, loses on 44, ties on 282; two-sided p = 0.6063 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

| seed | n | geometric mean | slower | faster |
|---|---:|---:|---:|---:|
| 4 | 2 | 0.866 | 0 | 2 |
| all (per instance) | 2 | 0.866 | 0 | 2 |

Per family (instances pooled over the seeds; `> 1.10` marks families of at least 3 instances with a geometric mean above 1.10):

| family | n | geometric mean | mark |
|---|---:|---:|---:|
| numeric | 2 | 0.866 |  |

Largest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 1.3.qcir | 0.878 | 9.09 | 7.98 |
| 1.4.qcir | 0.856 | 9.13 | 7.81 |

Smallest ratios:

| instance | ratio | A cpu s | B cpu s |
|---|---:|---:|---:|
| 1.4.qcir | 0.856 | 9.13 | 7.81 |
| 1.3.qcir | 0.878 | 9.09 | 7.98 |

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 4 | 85/69/154 | 74.9 | 85/68/153 | 75.3 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 154-154 | 74.9-74.9 |
| B | 153-153 | 75.3-75.3 |

## Instances gained and lost in a majority of seeds

- gained by B (5): `CM-sat-04-01-06-4.qcir`, `SR-sat-02-01-06-3.qcir`, `bt-2x5_17.ig.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir`, `jctc17-vals-0,2-pass.qcir`
- lost by B (6): `JP-unsat-02-06-3.qcir`, `bt2nd-3x4_12.ig.qcir`, `chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir`, `hadw11-12.qcir`, `jctc9-pass.qcir`, `nreachq_query71_1344.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 92.2 | 83.1 | -9.1 | 2 | 1 |
| DW | 7 | 14.9 | 12.5 | -2.4 | 4 | 2 |
| DWs | 13 | 113.2 | 114.6 | +1.4 | 0 | 1 |
| JP | 6 | 102.6 | 120.0 | +17.4 | 0 | 1 |
| Lights | 2 | 32.7 | 32.8 | +0.2 | 1 | 1 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 104.2 | 85.1 | -19.1 | 1 | 1 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 84.0 | 83.9 | -0.1 | 1 | 0 |
| arbiter | 6 | 84.5 | 83.6 | -0.9 | 1 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 69.4 | 70.4 | +1.1 | 2 | 2 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 60.7 | 60.8 | +0.1 | 6 | 9 |
| ci | 30 | 88.5 | 88.3 | -0.2 | 1 | 1 |
| collector | 1 | 3.4 | 2.3 | -1.1 | 1 | 0 |
| connect | 7 | 87.1 | 87.5 | +0.4 | 0 | 1 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 64.7 | 64.4 | -0.3 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.7 | 5.8 | -1.9 | 1 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 67.5 | 73.1 | +5.6 | 2 | 4 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 65.4 | 66.4 | +1.0 | 3 | 2 |
| klieber | 26 | 13.8 | 13.6 | -0.2 | 9 | 11 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.5 | 60.6 | +0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | -0.0 | 0 | 0 |
| ltl | 5 | 99.1 | 98.5 | -0.6 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 111.2 | 109.7 | -1.5 | 1 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 0.5 | 120.0 | +119.5 | 0 | 1 |
| numeric | 26 | 38.1 | 37.6 | -0.5 | 6 | 2 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 41.4 | 42.9 | +1.6 | 1 | 1 |
| robot | 1 | 6.3 | 2.0 | -4.3 | 1 | 0 |
| round | 1 | 0.9 | 1.6 | +0.7 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 55.1 | 55.2 | +0.1 | 1 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 34.3 | 33.7 | -0.6 | 4 | 3 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc17-vals-0,2-pass.qcir | 120.0 | 16.0 | -104.0 |
| SR-sat-02-01-06-3.qcir | 120.0 | 20.0 | -100.0 |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 120.0 | 44.4 | -75.6 |
| CM-sat-04-01-06-4.qcir | 120.0 | 58.4 | -61.6 |
| bt-2x5_17.ig.qcir | 120.0 | 59.2 | -60.8 |
| CM-sat-04-01-07-3.qcir | 36.9 | 5.4 | -31.5 |
| test_5_5_knobby.pg-9.qcir | 21.4 | 2.9 | -18.4 |
| klieber2017q-086-21-t1.qcir | 37.4 | 22.4 | -15.1 |
| mult9.sat.qcir | 40.5 | 27.0 | -13.5 |
| DW-sat-08-22-1.qcir | 22.2 | 9.5 | -12.6 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| jctc9-pass.qcir | 0.4 | 120.0 | +119.6 |
| nreachq_query71_1344.qcir | 0.5 | 120.0 | +119.5 |
| JP-unsat-02-06-3.qcir | 15.6 | 120.0 | +104.4 |
| hadw11-12.qcir | 20.8 | 120.0 | +99.2 |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 43.4 | 120.0 | +76.6 |
| bt2nd-3x4_12.ig.qcir | 57.8 | 120.0 | +62.2 |
| klieber2017q-112-28-t1.qcir | 14.8 | 51.7 | +36.9 |
| CM-sat-04-01-06-3.qcir | 8.6 | 38.1 | +29.5 |
| hadw7-9.qcir | 28.7 | 46.7 | +18.0 |
| DWs-unsat-08-17-1.qcir | 31.4 | 49.2 | +17.8 |

## Peak memory

12 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| klieber2017q-112-28-t1.qcir | 18 | 28 | 1.62x |
| CM-sat-04-01-06-3.qcir | 157 | 210 | 1.34x |
| reachqu_query64_1344.qcir | 27 | 36 | 1.31x |
| test_5_5_el.pg-13.qcir | 30 | 39 | 1.28x |
| hadw8-9.qcir | 28 | 36 | 1.27x |
| klieber2017q-100-25-t1.qcir | 16 | 19 | 1.24x |
| connect-4x4_9_connect3.ig.qcir | 25 | 29 | 1.16x |
| klieber2017q-074-18-t1.qcir | 12 | 14 | 1.14x |
| test_5_5_skinny.pg-9.qcir | 21 | 24 | 1.14x |
| test_5_5_domino.pg-13.qcir | 12 | 14 | 1.13x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | 34 | 38 | 1.11x |
| chess_solving_mate_in_2_2011_ISC-7B_01.qcir | 34 | 38 | 1.11x |

