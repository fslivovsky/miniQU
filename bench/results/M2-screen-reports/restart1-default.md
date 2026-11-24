# Paired comparison: B (M2-screen-restart1-default-s4) against A (M2-screen-ref-default-s4)

No result discrepancies, solver errors or proof problems.

## Parameters

jobs 24, mem_gb 8, cores 24-47, timeout 60.0 s, 376 instances compared, seeds [4].

| arm | args | git | sha256 | date |
|---|---:|---:|---:|---:|
| A | `` | 49df19e | 0c2f34956a22 | 2026-11-24T11:43:52 |
| B | `--restartmode=1` | 49df19e+dirty | 0c2f34956a22 | 2026-11-24T12:27:19 |

Order in which the runs started:

- 2026-11-24T11:43:52 `M2-screen-ref-default-s4`
- 2026-11-24T12:27:19 `M2-screen-restart1-default-s4`

## Result

PAR2 difference (B - A, mean over 376 instances, scores are means over 1 seeds): **+0.84 s**, 95% bootstrap interval [-0.35, +2.06] (10000 resamples).

Sign test: B wins on 30 instances, loses on 46, ties on 300; two-sided p = 0.0846 (margin max(1 s, 10% of the smaller score)).

**Verdict: no measurable difference.**

B is not worse than A: **yes**.

## Identical searches

Instances that both arms solved with the same result and the same number of conflicts (A used more than 1 s of CPU time) ran the same search, so the CPU-time ratio B / A measures engine speed alone.

no instance with equal conflict counts

## Per seed (SAT/UNSAT/total solved, PAR2 in s)

| seed | A solved | A PAR2 | B solved | B PAR2 |
|---|---:|---:|---:|---:|
| 4 | 92/63/155 | 75.2 | 91/62/153 | 76.0 |

Noise band (spread over the seeds of one arm):

| arm | solved | PAR2 |
|---|---:|---:|
| A | 155-155 | 75.2-75.2 |
| B | 153-153 | 76.0-76.0 |

## Instances gained and lost in a majority of seeds

- gained by B (2): `CM-sat-04-01-06-3.qcir`, `klieber2017q-076-19-t1.qcir`
- lost by B (4): `5.2-1.qcir`, `DW-unsat-10-25-1.qcir`, `klieber2017q-084-21-eq.qcir`, `klieber2017q-086-21-t1.qcir`

## Per family (mean score in s)

| family | n | A | B | B - A | wins | losses |
|---|---:|---:|---:|---:|---:|---:|
| CM | 7 | 120.0 | 107.4 | -12.6 | 1 | 0 |
| DW | 7 | 30.7 | 38.3 | +7.6 | 3 | 2 |
| DWs | 13 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| JP | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Lights | 2 | 80.9 | 81.7 | +0.7 | 0 | 0 |
| LightsTotal | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| SR | 5 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| Sensor | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| abcg | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| add | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| adder | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| amba | 5 | 85.4 | 88.3 | +2.9 | 0 | 2 |
| arbiter | 6 | 83.6 | 83.8 | +0.2 | 0 | 0 |
| auto | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bar | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemldelec | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| beemskbn | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bs | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| bt | 12 | 48.5 | 48.0 | -0.5 | 2 | 1 |
| cavlc | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| chess | 40 | 26.9 | 27.6 | +0.7 | 2 | 7 |
| ci | 30 | 100.2 | 101.3 | +1.2 | 0 | 4 |
| collector | 1 | 4.0 | 2.9 | -1.2 | 1 | 0 |
| connect | 7 | 74.3 | 72.1 | -2.2 | 1 | 0 |
| cycle | 7 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| driver | 6 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| ea | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| eequery | 2 | 69.4 | 73.8 | +4.4 | 0 | 1 |
| ex | 10 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finan | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| finding | 1 | 7.5 | 8.1 | +0.6 | 0 | 0 |
| genbuf | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| hadw | 21 | 70.9 | 72.3 | +1.4 | 2 | 3 |
| i | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| jctc | 13 | 66.5 | 66.6 | +0.1 | 0 | 1 |
| klieber | 26 | 44.2 | 48.1 | +3.9 | 10 | 11 |
| l | 8 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| lift | 2 | 60.7 | 60.6 | -0.1 | 0 | 0 |
| linux | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| load | 5 | 96.2 | 96.2 | +0.0 | 0 | 0 |
| ltl | 5 | 98.7 | 97.0 | -1.7 | 1 | 0 |
| max | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mem | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| mult | 9 | 110.6 | 110.4 | -0.3 | 0 | 0 |
| myciel | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| nreachq | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| numeric | 26 | 28.5 | 32.7 | +4.2 | 3 | 6 |
| prioritized | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| priority | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| reachqu | 3 | 40.6 | 54.9 | +14.3 | 0 | 2 |
| robot | 1 | 2.6 | 1.3 | -1.3 | 1 | 0 |
| round | 1 | 1.4 | 0.9 | -0.5 | 0 | 0 |
| router | 4 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| s | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| sc | 9 | 56.0 | 56.4 | +0.4 | 1 | 2 |
| simple | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| square | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| stay | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| test | 28 | 35.4 | 35.6 | +0.2 | 2 | 4 |
| voter | 2 | 120.0 | 120.0 | +0.0 | 0 | 0 |
| workstation | 1 | 120.0 | 120.0 | +0.0 | 0 | 0 |

## Largest differences

B faster:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-076-19-t1.qcir | 120.0 | 16.7 | -103.3 |
| CM-sat-04-01-06-3.qcir | 120.0 | 32.0 | -88.0 |
| klieber2017q-074-18-eq.qcir | 38.7 | 21.4 | -17.3 |
| klieber2017q-082-20-t1.qcir | 45.4 | 28.6 | -16.8 |
| connect-5x5_9_connect3.ig.qcir | 35.7 | 20.5 | -15.2 |
| klieber2017q-070-17-eq.qcir | 24.9 | 12.4 | -12.5 |
| hadw6-8.qcir | 24.8 | 12.7 | -12.0 |
| klieber2017q-064-16-eq.qcir | 17.1 | 7.9 | -9.2 |
| DW-unsat-09-23-1.qcir | 19.7 | 10.6 | -9.2 |
| klieber2017q-074-18-t1.qcir | 19.9 | 10.8 | -9.1 |

B slower:

| instance | A score | B score | B - A |
|---|---:|---:|---:|
| klieber2017q-086-21-t1.qcir | 16.2 | 120.0 | +103.8 |
| 5.2-1.qcir | 29.9 | 120.0 | +90.1 |
| DW-unsat-10-25-1.qcir | 51.4 | 120.0 | +68.6 |
| klieber2017q-084-21-eq.qcir | 57.9 | 120.0 | +62.1 |
| klieber2017q-066-16-eq.qcir | 22.8 | 57.6 | +34.9 |
| klieber2017q-078-19-t1.qcir | 14.8 | 47.4 | +32.5 |
| reachqu_query64_1344.qcir | 1.7 | 27.9 | +26.3 |
| hadw11-12.qcir | 5.8 | 32.0 | +26.1 |
| reachqu_query60_1344.qcir | 0.2 | 16.7 | +16.5 |
| klieber2017q-084-21-t1.qcir | 26.7 | 40.4 | +13.7 |

## Peak memory

34 instances solved by both arms in every seed where B's peak RSS exceeds A's by more than 10%.

| instance | A MB | B MB | ratio |
|---|---:|---:|---:|
| hadw10-11.qcir | 78 | 180 | 2.32x |
| hadw9-10.qcir | 45 | 96 | 2.12x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | 12 | 21 | 1.69x |
| reachqu_query60_1344.qcir | 16 | 26 | 1.69x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | 12 | 20 | 1.62x |
| hadw11-12.qcir | 147 | 237 | 1.61x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | 12 | 19 | 1.58x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | 51 | 80 | 1.57x |
| hadw8-9.qcir | 23 | 36 | 1.57x |
| reachqu_query64_1344.qcir | 20 | 30 | 1.47x |
| klieber2017q-064-16-t1.qcir | 16 | 22 | 1.39x |
| test_5_5_skinny.pg-9.qcir | 15 | 20 | 1.39x |
| klieber2017q-084-21-t1.qcir | 22 | 30 | 1.37x |
| klieber2017q-078-19-t1.qcir | 18 | 24 | 1.36x |
| bt-3x6_9.ig.qcir | 35 | 46 | 1.33x |
| finding_nemo_1.tlsf.qcir | 24 | 32 | 1.32x |
| arbiter_on_inpchange5.tlsf.qcir | 19 | 24 | 1.27x |
| hadw7-8.qcir | 17 | 21 | 1.27x |
| bt2nd-2x5_10.ig.qcir | 20 | 25 | 1.26x |
| connect-3x3_9_connect3.ig.qcir | 15 | 19 | 1.26x |
| jctc6-pass.qcir | 45 | 56 | 1.25x |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | 54 | 66 | 1.24x |
| test_5_5_snaky.pg-9.qcir | 29 | 36 | 1.24x |
| klieber2017q-072-18-eq.qcir | 25 | 31 | 1.21x |
| sc-ungrounded-2x1X1x2_2.qcir | 25 | 30 | 1.21x |
| ci.e#1.a#3.E#40.A#60.c#424.w#2.s#1.asp.qcir | 12 | 14 | 1.18x |
| klieber2017q-076-19-eq.qcir | 35 | 41 | 1.17x |
| klieber2017q-068-17-eq.qcir | 17 | 19 | 1.15x |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 44 | 50 | 1.14x |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 44 | 50 | 1.13x |

