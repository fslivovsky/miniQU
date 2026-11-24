# Paired comparison: B (M2-screen-ccmin3-default-s4) against A (M2-screen-ref-default-s4)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [4].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | 49df19e | 0c2f34956a22 | 2026-11-24T11:43:52 |
| B | `--ccminmode=3` | 49df19e+dirty | 0c2f34956a22 | 2026-11-24T12:05:30 |

Order in which the runs started:

- 2026-11-24T11:43:52 `M2-screen-ref-default-s4`
- 2026-11-24T12:05:30 `M2-screen-ccmin3-default-s4`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **+1.26 s**, 95% bootstrap interval [-0.22, +2.84] (10000 resamples).

Sign test: B wins on 28 instances, loses on 32, ties on 316; two-sided p = 0.6989 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

no instance with equal conflict counts

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 4 | 92/63/155 | 75.2 | 88/61/149 | 76.4 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 155-155 | 75.2-75.2 |
| B | 149-149 | 76.4-76.4 |

## Instances gained and lost in a majority of seeds

- gained by B (2): `chess_composing_8_template_43.qcir`, `jctc14-unrolled-fail.qcir`
- lost by B (8): `5.1-1.qcir`, `DW-unsat-10-25-1.qcir`, `bt2nd-2x6_14.ig.qcir`, `klieber2017q-066-16-eq.qcir`, `klieber2017q-084-21-eq.qcir`, `klieber2017q-086-21-t1.qcir`, `reachqu_query64_1344.qcir`, `test_5_5_el.pg-13.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| DW | 7 | 30.7 | 40.3 | +9.6 | 1 | 3 |
| DWs | 13 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 80.9 | 78.4 | -2.5 | 1 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 85.4 | 85.6 | +0.1 | 0 | 0 |
| arbiter | 6 | 83.6 | 83.7 | +0.1 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 48.5 | 53.8 | +5.3 | 1 | 3 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 26.9 | 26.2 | -0.7 | 2 | 8 |
| ci | 30 | 100.2 | 100.6 | +0.5 | 0 | 2 |
| collector | 1 | 4.0 | 2.5 | -1.5 | 1 | 0 |
| connect | 7 | 74.3 | 74.9 | +0.6 | 0 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 69.4 | 69.7 | +0.3 | 0 | 0 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.5 | 7.0 | -0.5 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 70.9 | 70.3 | -0.6 | 1 | 0 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 66.5 | 59.8 | -6.6 | 3 | 0 |
| klieber | 26 | 44.2 | 53.2 | +9.1 | 7 | 9 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.7 | 60.6 | -0.2 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | +0.0 | 0 | 0 |
| ltl | 5 | 98.7 | 96.7 | -2.0 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.6 | 109.5 | -1.1 | 1 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 28.5 | 30.6 | +2.2 | 4 | 4 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 40.6 | 80.3 | +39.7 | 0 | 1 |
| robot | 1 | 2.6 | 1.7 | -0.9 | 0 | 0 |
| round | 1 | 1.4 | 1.1 | -0.3 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.0 | 55.2 | -0.8 | 2 | 0 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 35.4 | 38.0 | +2.6 | 3 | 2 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| chess_composing_8_template_43.qcir | 120.0 | 16.1 | -103.9 |
| jctc14-unrolled-fail.qcir | 120.0 | 38.1 | -81.9 |
| klieber2017q-082-20-t1.qcir | 45.4 | 7.0 | -38.3 |
| 5.2-2.qcir | 55.4 | 22.4 | -33.1 |
| klieber2017q-080-20-t1.qcir | 48.1 | 20.5 | -27.6 |
| klieber2017q-084-21-t1.qcir | 26.7 | 7.7 | -19.1 |
| klieber2017q-078-19-eq.qcir | 30.2 | 18.7 | -11.6 |
| klieber2017q-064-16-t1.qcir | 23.7 | 12.3 | -11.4 |
| DW-unsat-09-23-1.qcir | 19.7 | 8.5 | -11.2 |
| hadw6-8.qcir | 24.8 | 13.6 | -11.2 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| reachqu_query64_1344.qcir | 1.7 | 120.0 | +118.3 |
| klieber2017q-086-21-t1.qcir | 16.2 | 120.0 | +103.8 |
| klieber2017q-066-16-eq.qcir | 22.8 | 120.0 | +97.2 |
| test_5_5_el.pg-13.qcir | 32.7 | 120.0 | +87.3 |
| 5.1-1.qcir | 42.8 | 120.0 | +77.2 |
| DW-unsat-10-25-1.qcir | 51.4 | 120.0 | +68.6 |
| klieber2017q-084-21-eq.qcir | 57.9 | 120.0 | +62.1 |
| bt2nd-2x6_14.ig.qcir | 58.8 | 120.0 | +61.2 |
| klieber2017q-078-19-t1.qcir | 14.8 | 50.7 | +35.9 |
| klieber2017q-076-19-eq.qcir | 29.5 | 57.6 | +28.1 |

## Peak memory

9 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | 12 | 20 | 1.61x |
| klieber2017q-078-19-t1.qcir | 18 | 26 | 1.50x |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 54 | 75 | 1.39x |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 55 | 64 | 1.16x |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 44 | 51 | 1.16x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | 12 | 14 | 1.16x |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 44 | 50 | 1.14x |
| klieber2017q-072-18-t1.qcir | 22 | 25 | 1.13x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 31 | 34 | 1.12x |

