# Benchmark comparison: baseline-t180 vs baseline-dl-t180

No result discrepancies, solver errors or proof problems.

376 common instances compared (376 in the union).

## Summary

| run | SAT | UNSAT | solved | total | PAR2 | wall sum (solved) s | cpu sum (solved) s | max RSS MB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| baseline-t180 | 100 | 67 | 167 | 376 | 209.9 | 3668 | 3664 | 8262 |
| baseline-dl-t180 | 96 | 72 | 168 | 376 | 208.5 | 3521 | 3495 | 8227 |

| run | git | args | timeout | date |
|---|---:|---:|---:|---:|
| baseline-t180 | c39005a | `` | 180.0 | 2026-11-21T16:46:30 |
| baseline-dl-t180 | c39005a | `-dl` | 180.0 | 2026-11-21T17:56:52 |

## Uniquely solved

- **baseline-t180** only (14): `5.1-1.qcir` (40.0s), `chess_solving_mate_in_3_2000_CZE-CH_04.qcir` (12.3s), `chess_solving_mate_in_3_2001_UKR-CH_06.qcir` (21.0s), `chess_solving_mate_in_3_2003_UKR-CH_04.qcir` (19.5s), `chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir` (13.1s), `chess_solving_mate_in_3_2014_FRA-CH_03.qcir` (9.5s), `chess_solving_mate_in_4_2001_UKR-CH_13.qcir` (13.1s), `connect-5x5_9_connect3.ig.qcir` (72.1s), `connect-6x6_9_connect3.ig.qcir` (49.2s), `hadw11-12.qcir` (6.5s), `jctc10-fail.qcir` (5.4s), `jctc14-unrolled-fail.qcir` (33.0s), `jctc2-pass.qcir` (1.5s), `jctc8-pass.qcir` (0.1s)
- **baseline-dl-t180** only (15): `CM-sat-04-01-06-4.qcir` (29.7s), `CM-sat-04-01-07-3.qcir` (34.3s), `CM-sat-07-01-07-3.qcir` (45.0s), `DWs-sat-10-23-1.qcir` (171.2s), `DWs-unsat-08-17-1.qcir` (31.1s), `DWs-unsat-08-18-1.qcir` (168.3s), `JP-unsat-02-06-3.qcir` (53.4s), `SR-unsat-04-01-08-1.qcir` (81.7s), `ci.e#1.a#3.E#40.A#60.c#200.w#6.s#6.asp.qcir` (0.3s), `ci.e#1.a#3.E#40.A#60.c#208.w#6.s#8.asp.qcir` (4.3s), `ci.e#1.a#3.E#40.A#60.c#264.w#4.s#2.asp.qcir` (16.9s), `hadw6-8.qcir` (6.3s), `hadw7-9.qcir` (165.6s), `jctc5-fail.qcir` (7.5s), `klieber2017q-112-28-t1.qcir` (25.3s)


## Per family (solved / total)

| family | n | baseline-t180 | baseline-dl-t180 | PAR2 baseline-t180 | PAR2 baseline-dl-t180 |
|---|---:|---:|---:|---:|---:|
| CM | 7 | 1 | 4 | 318.3 | 170.7 |
| DW | 7 | 7 | 7 | 18.7 | 11.7 |
| DWs | 13 | 0 | 3 | 360.0 | 305.4 |
| JP | 6 | 0 | 1 | 360.0 | 308.9 |
| Lights | 2 | 2 | 2 | 59.4 | 46.4 |
| LightsTotal | 1 | 0 | 0 | 360.0 | 360.0 |
| SR | 5 | 0 | 1 | 360.0 | 304.3 |
| Sensor | 1 | 0 | 0 | 360.0 | 360.0 |
| abcg | 1 | 0 | 0 | 360.0 | 360.0 |
| add | 1 | 0 | 0 | 360.0 | 360.0 |
| adder | 1 | 0 | 0 | 360.0 | 360.0 |
| amba | 5 | 2 | 2 | 238.0 | 230.2 |
| arbiter | 6 | 2 | 2 | 244.4 | 244.3 |
| auto | 10 | 0 | 0 | 360.0 | 360.0 |
| bar | 1 | 0 | 0 | 360.0 | 360.0 |
| beemldelec | 1 | 0 | 0 | 360.0 | 360.0 |
| beemskbn | 1 | 0 | 0 | 360.0 | 360.0 |
| bs | 2 | 0 | 0 | 360.0 | 360.0 |
| bt | 12 | 8 | 8 | 159.8 | 160.6 |
| cavlc | 1 | 0 | 0 | 360.0 | 360.0 |
| chess | 40 | 32 | 26 | 75.3 | 140.5 |
| ci | 30 | 5 | 8 | 300.1 | 264.8 |
| collector | 1 | 1 | 1 | 4.0 | 4.8 |
| connect | 7 | 4 | 2 | 172.6 | 259.3 |
| cycle | 7 | 0 | 0 | 360.0 | 360.0 |
| driver | 6 | 0 | 0 | 360.0 | 360.0 |
| ea | 2 | 0 | 0 | 360.0 | 360.0 |
| eequery | 2 | 1 | 1 | 199.4 | 188.7 |
| ex | 10 | 0 | 0 | 360.0 | 360.0 |
| finan | 2 | 0 | 0 | 360.0 | 360.0 |
| finding | 1 | 1 | 1 | 13.2 | 10.3 |
| genbuf | 2 | 0 | 0 | 360.0 | 360.0 |
| hadw | 21 | 8 | 9 | 225.7 | 217.8 |
| i | 4 | 0 | 0 | 360.0 | 360.0 |
| jctc | 13 | 12 | 9 | 32.7 | 114.3 |
| klieber | 26 | 25 | 26 | 63.2 | 16.0 |
| l | 8 | 0 | 0 | 360.0 | 360.0 |
| lift | 2 | 1 | 1 | 181.2 | 181.3 |
| linux | 2 | 0 | 0 | 360.0 | 360.0 |
| load | 5 | 1 | 1 | 288.3 | 288.3 |
| ltl | 5 | 1 | 1 | 290.0 | 291.6 |
| max | 1 | 0 | 0 | 360.0 | 360.0 |
| mem | 1 | 0 | 0 | 360.0 | 360.0 |
| mult | 9 | 1 | 1 | 326.4 | 325.5 |
| myciel | 2 | 0 | 0 | 360.0 | 360.0 |
| nreachq | 1 | 0 | 0 | 360.0 | 360.0 |
| numeric | 26 | 22 | 21 | 66.5 | 81.1 |
| prioritized | 2 | 0 | 0 | 360.0 | 360.0 |
| priority | 1 | 0 | 0 | 360.0 | 360.0 |
| reachqu | 3 | 1 | 1 | 248.9 | 240.2 |
| robot | 1 | 1 | 1 | 6.4 | 2.0 |
| round | 1 | 1 | 1 | 1.5 | 1.8 |
| router | 4 | 0 | 0 | 360.0 | 360.0 |
| s | 1 | 0 | 0 | 360.0 | 360.0 |
| sc | 9 | 5 | 5 | 164.2 | 166.0 |
| simple | 1 | 0 | 0 | 360.0 | 360.0 |
| square | 1 | 0 | 0 | 360.0 | 360.0 |
| stay | 1 | 0 | 0 | 360.0 | 360.0 |
| test | 28 | 22 | 22 | 97.7 | 89.1 |
| voter | 2 | 0 | 0 | 360.0 | 360.0 |
| workstation | 1 | 0 | 0 | 360.0 | 360.0 |

## baseline-dl-t180 relative to baseline-t180 (153 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.89x**.

Top 5 speedups:

| instance | result | baseline-t180 s | baseline-dl-t180 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_snaky.pg-9.qcir | UNSAT | 113.60 | 0.07 | 1135.97x |
| test_5_5_Z.pg-7.qcir | UNSAT | 5.92 | 0.10 | 59.21x |
| reachqu_query64_1344.qcir | SAT | 26.81 | 0.48 | 55.75x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 3.76 | 0.06 | 37.63x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.41 | 0.04 | 24.12x |

Top 5 regressions:

| instance | result | baseline-t180 s | baseline-dl-t180 s | speedup |
|---|---:|---:|---:|---:|
| jctc1-pass.qcir | SAT | 0.13 | 8.64 | 0.01x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.41 | 13.44 | 0.03x |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | SAT | 2.51 | 71.63 | 0.03x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.62 | 14.73 | 0.04x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 3.06 | 64.10 | 0.05x |

## Proof checking (Lean qlrup-check)

| run | checked | verified | other statuses | check s (sum) | check s (max) | proof MB (sum) | proof MB (max) |
|---|---:|---:|---:|---:|---:|---:|---:|
| baseline-t180 | 115 | 115 | - | 1422.8 | 251.6 | 3682.2 | 227.0 |

