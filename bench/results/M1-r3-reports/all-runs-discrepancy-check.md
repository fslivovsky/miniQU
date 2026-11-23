# Benchmark comparison: baseline-c96-default-t60-s1 vs M1-r3-default-s1 vs M1-r3-default-s2 vs M1-r3-default-s3 vs M1-r3-dl-s1 vs M1-r3-dl-s2 vs M1-r3-dl-s3 vs M1-r3-mode1-s1 vs M1-r3-mode2-s1 vs M1-r3-ccmin3-s1 vs baseline-t180

No result discrepancies, solver errors or proof problems.

376 common instances compared (376 in the union).
**Warning:** timeouts differ between runs: {'baseline-c96-default-t60-s1': 60.0, 'M1-r3-default-s1': 60.0, 'M1-r3-default-s2': 60.0, 'M1-r3-default-s3': 60.0, 'M1-r3-dl-s1': 60.0, 'M1-r3-dl-s2': 60.0, 'M1-r3-dl-s3': 60.0, 'M1-r3-mode1-s1': 60.0, 'M1-r3-mode2-s1': 60.0, 'M1-r3-ccmin3-s1': 60.0, 'baseline-t180': 180.0}

## Summary

| run | SAT | UNSAT | solved | total | PAR2 | wall sum (solved) s | cpu sum (solved) s | max RSS MB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| baseline-c96-default-t60-s1 | 82 | 59 | 141 | 376 | 79.3 | 1628 | 1625 | 8245 |
| M1-r3-default-s1 | 83 | 59 | 142 | 376 | 79.7 | 1872 | 1869 | 8199 |
| M1-r3-default-s2 | 86 | 59 | 145 | 376 | 78.0 | 1613 | 1610 | 8219 |
| M1-r3-default-s3 | 83 | 60 | 143 | 376 | 78.7 | 1630 | 1628 | 8213 |
| M1-r3-dl-s1 | 85 | 64 | 149 | 376 | 76.5 | 1524 | 1520 | 8201 |
| M1-r3-dl-s2 | 88 | 65 | 153 | 376 | 75.6 | 1665 | 1662 | 8216 |
| M1-r3-dl-s3 | 83 | 63 | 146 | 376 | 77.4 | 1489 | 1485 | 8208 |
| M1-r3-mode1-s1 | 72 | 43 | 115 | 376 | 86.1 | 1037 | 1035 | 8198 |
| M1-r3-mode2-s1 | 78 | 57 | 135 | 376 | 80.9 | 1490 | 1487 | 8215 |
| M1-r3-ccmin3-s1 | 87 | 60 | 147 | 376 | 77.5 | 1663 | 1660 | 8207 |
| baseline-t180 | 100 | 67 | 167 | 376 | 209.9 | 3668 | 3664 | 8262 |

| run | git | args | timeout | date |
|---|---:|---:|---:|---:|
| baseline-c96-default-t60-s1 | c39005a | `` | 60.0 | 2026-11-23T01:16:03 |
| M1-r3-default-s1 | 46874d9 | `` | 60.0 | 2026-11-23T20:12:40 |
| M1-r3-default-s2 | 46874d9 | `` | 60.0 | 2026-11-23T20:18:43 |
| M1-r3-default-s3 | 46874d9 | `` | 60.0 | 2026-11-23T20:24:43 |
| M1-r3-dl-s1 | 46874d9 | `-dl` | 60.0 | 2026-11-23T20:30:44 |
| M1-r3-dl-s2 | 46874d9 | `-dl` | 60.0 | 2026-11-23T20:36:39 |
| M1-r3-dl-s3 | 46874d9 | `-dl` | 60.0 | 2026-11-23T20:42:30 |
| M1-r3-mode1-s1 | 46874d9 | `-mode=1` | 60.0 | 2026-11-23T20:48:28 |
| M1-r3-mode2-s1 | 46874d9 | `-mode=2` | 60.0 | 2026-11-23T20:54:38 |
| M1-r3-ccmin3-s1 | 46874d9 | `-ccmin-mode=3` | 60.0 | 2026-11-23T21:00:38 |
| baseline-t180 | c39005a | `` | 180.0 | 2026-11-21T16:46:30 |

## Uniquely solved

- **M1-r3-dl-s1** only (2): `CM-sat-07-01-07-3.qcir` (50.6s), `voter_size_202219_1U43.qcir` (11.9s)
- **M1-r3-dl-s2** only (1): `SR-sat-02-01-06-3.qcir` (27.3s)
- **M1-r3-mode1-s1** only (1): `hadw4-7.qcir` (55.1s)
- **M1-r3-mode2-s1** only (3): `DWs-unsat-08-17-1.qcir` (43.0s), `DWs-unsat-08-18-1.qcir` (11.9s), `hadw2-8.qcir` (48.9s)
- **M1-r3-ccmin3-s1** only (1): `DWs-sat-12-28-1.qcir` (1.9s)
- **baseline-t180** only (4): `bt-3x4_19.ig.qcir` (116.1s), `connect-5x5_9_connect3.ig.qcir` (72.1s), `connect-6x6_9_connect3.ig.qcir` (49.2s), `jctc14-unrolled-fail.qcir` (33.0s)


## Per family (solved / total)

| family | n | baseline-c96-default-t60-s1 | M1-r3-default-s1 | M1-r3-default-s2 | M1-r3-default-s3 | M1-r3-dl-s1 | M1-r3-dl-s2 | M1-r3-dl-s3 | M1-r3-mode1-s1 | M1-r3-mode2-s1 | M1-r3-ccmin3-s1 | baseline-t180 | PAR2 baseline-c96-default-t60-s1 | PAR2 M1-r3-default-s1 | PAR2 M1-r3-default-s2 | PAR2 M1-r3-default-s3 | PAR2 M1-r3-dl-s1 | PAR2 M1-r3-dl-s2 | PAR2 M1-r3-dl-s3 | PAR2 M1-r3-mode1-s1 | PAR2 M1-r3-mode2-s1 | PAR2 M1-r3-ccmin3-s1 | PAR2 baseline-t180 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| CM | 7 | 1 | 2 | 1 | 0 | 3 | 2 | 2 | 1 | 1 | 1 | 1 | 103.0 | 93.5 | 103.2 | 120.0 | 82.7 | 94.0 | 88.4 | 103.1 | 103.2 | 104.8 | 318.3 |
| DW | 7 | 6 | 6 | 6 | 6 | 7 | 6 | 7 | 5 | 5 | 6 | 7 | 32.7 | 34.0 | 30.2 | 28.2 | 15.1 | 26.2 | 13.4 | 39.7 | 40.1 | 31.2 | 18.7 |
| DWs | 13 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 3 | 1 | 0 | 120.0 | 120.0 | 120.0 | 111.9 | 120.0 | 120.0 | 120.0 | 120.0 | 96.7 | 110.9 | 360.0 |
| JP | 6 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 0 | 1 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 109.1 | 109.2 | 120.0 | 108.7 | 120.0 | 360.0 |
| Lights | 2 | 1 | 1 | 1 | 1 | 2 | 2 | 1 | 1 | 1 | 2 | 2 | 86.9 | 88.2 | 79.3 | 73.6 | 38.5 | 44.9 | 72.6 | 87.6 | 73.9 | 55.2 | 59.4 |
| LightsTotal | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| SR | 5 | 0 | 0 | 0 | 0 | 0 | 2 | 1 | 0 | 1 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 86.5 | 105.4 | 120.0 | 97.3 | 120.0 | 360.0 |
| Sensor | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| abcg | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| add | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| adder | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| amba | 5 | 1 | 1 | 1 | 1 | 2 | 2 | 1 | 1 | 0 | 2 | 2 | 100.8 | 100.8 | 101.0 | 100.6 | 86.7 | 87.4 | 99.9 | 101.7 | 120.0 | 87.6 | 238.0 |
| arbiter | 6 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 2 | 2 | 84.6 | 84.2 | 84.9 | 84.3 | 83.5 | 83.8 | 84.5 | 85.0 | 120.0 | 83.5 | 244.4 |
| auto | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| bar | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| beemldelec | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| beemskbn | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| bs | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| bt | 12 | 4 | 5 | 6 | 5 | 4 | 4 | 4 | 3 | 3 | 4 | 8 | 84.6 | 80.3 | 74.9 | 77.5 | 83.6 | 83.7 | 83.3 | 93.7 | 91.3 | 84.1 | 159.8 |
| cavlc | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| chess | 40 | 32 | 32 | 32 | 32 | 21 | 21 | 20 | 32 | 31 | 32 | 32 | 27.2 | 27.8 | 27.0 | 27.7 | 62.0 | 60.5 | 63.4 | 29.4 | 31.0 | 28.7 | 75.3 |
| ci | 30 | 5 | 5 | 5 | 5 | 8 | 8 | 8 | 5 | 8 | 5 | 5 | 100.1 | 100.2 | 100.1 | 100.1 | 89.3 | 88.2 | 88.3 | 100.1 | 88.8 | 100.1 | 300.1 |
| collector | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 3.2 | 2.9 | 4.9 | 4.3 | 4.1 | 3.8 | 3.4 | 3.4 | 7.2 | 2.6 | 4.0 |
| connect | 7 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 2 | 4 | 87.4 | 87.0 | 86.9 | 86.5 | 87.3 | 88.4 | 87.2 | 89.1 | 120.0 | 86.9 | 172.6 |
| cycle | 7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| driver | 6 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| ea | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| eequery | 2 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 75.4 | 78.9 | 81.1 | 77.4 | 68.6 | 69.6 | 72.2 | 72.2 | 65.6 | 73.3 | 199.4 |
| ex | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| finan | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| finding | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 12.3 | 11.3 | 8.8 | 8.6 | 7.7 | 7.8 | 7.8 | 9.3 | 40.9 | 7.9 | 13.2 |
| genbuf | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| hadw | 21 | 8 | 8 | 8 | 8 | 8 | 9 | 7 | 9 | 9 | 8 | 8 | 76.3 | 76.0 | 76.1 | 75.8 | 78.0 | 74.0 | 82.1 | 72.2 | 72.1 | 75.9 | 225.7 |
| i | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| jctc | 13 | 5 | 5 | 7 | 3 | 9 | 10 | 9 | 5 | 4 | 6 | 12 | 75.7 | 76.4 | 58.9 | 92.3 | 39.4 | 34.9 | 40.2 | 77.1 | 83.3 | 71.2 | 32.7 |
| klieber | 26 | 20 | 18 | 19 | 21 | 25 | 26 | 25 | 1 | 22 | 21 | 25 | 49.8 | 60.8 | 51.3 | 45.8 | 15.4 | 14.4 | 18.5 | 116.5 | 37.0 | 41.2 | 63.2 |
| l | 8 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| lift | 2 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 60.7 | 60.7 | 61.0 | 60.5 | 61.0 | 61.2 | 60.9 | 61.0 | 61.8 | 60.6 | 181.2 |
| linux | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| load | 5 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 96.2 | 96.2 | 96.3 | 96.2 | 96.2 | 96.2 | 96.2 | 96.2 | 96.8 | 96.2 | 288.3 |
| ltl | 5 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 98.2 | 98.1 | 99.5 | 98.0 | 98.7 | 99.1 | 98.7 | 97.8 | 106.9 | 97.3 | 290.0 |
| max | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| mem | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| mult | 9 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 1 | 111.0 | 112.5 | 111.4 | 111.8 | 110.7 | 112.4 | 111.5 | 110.8 | 120.0 | 109.9 | 326.4 |
| myciel | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| nreachq | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 120.0 | 120.0 | 0.1 | 120.0 | 120.0 | 0.2 | 120.0 | 120.0 | 0.7 | 120.0 | 360.0 |
| numeric | 26 | 20 | 20 | 21 | 21 | 19 | 19 | 20 | 21 | 21 | 20 | 22 | 34.7 | 34.9 | 30.0 | 31.5 | 36.9 | 37.6 | 35.7 | 32.0 | 31.6 | 34.5 | 66.5 |
| prioritized | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| priority | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| reachqu | 3 | 1 | 1 | 0 | 2 | 1 | 1 | 2 | 1 | 2 | 1 | 1 | 84.2 | 96.0 | 120.0 | 48.3 | 98.2 | 80.9 | 60.3 | 91.7 | 54.9 | 81.1 | 248.9 |
| robot | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 7.2 | 4.8 | 2.2 | 4.7 | 2.1 | 5.2 | 2.2 | 3.8 | 24.3 | 2.6 | 6.4 |
| round | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 2.0 | 1.8 | 2.0 | 1.7 | 1.4 | 0.6 | 1.9 | 1.4 | 2.6 | 1.9 | 1.5 |
| router | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| s | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| sc | 9 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 4 | 5 | 5 | 59.7 | 58.4 | 56.8 | 57.3 | 55.6 | 56.5 | 56.2 | 56.7 | 75.1 | 57.1 | 164.2 |
| simple | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| square | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| stay | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| test | 28 | 19 | 20 | 19 | 19 | 21 | 21 | 20 | 12 | 10 | 20 | 22 | 46.2 | 41.8 | 45.8 | 45.7 | 36.1 | 35.6 | 40.2 | 70.7 | 79.0 | 41.7 | 97.7 |
| voter | 2 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 66.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |
| workstation | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 |

## M1-r3-default-s1 relative to baseline-c96-default-t60-s1 (136 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.98x**.

Top 10 speedups:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-default-s1 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_domino.pg-13.qcir | SAT | 2.56 | 1.46 | 1.76x |
| test_5_5_knobby.pg-7.qcir | SAT | 4.73 | 3.02 | 1.57x |
| test_5_5_tic.pg-11.qcir | SAT | 15.20 | 9.72 | 1.56x |
| connect-3x3_9_connect3.ig.qcir | UNSAT | 1.71 | 1.11 | 1.54x |
| klieber2017q-064-16-eq.qcir | SAT | 19.58 | 12.84 | 1.52x |
| robot_grid6_1.tlsf.qcir | SAT | 7.19 | 4.78 | 1.50x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.19 | 0.12 | 1.50x |
| klieber2017q-068-17-eq.qcir | SAT | 13.64 | 9.41 | 1.45x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 1.41 | 1.43x |
| sc-ungrounded-2x1X1x2_2.qcir | UNSAT | 11.48 | 8.05 | 1.42x |

Top 10 regressions:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-default-s1 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-084-21-t1.qcir | UNSAT | 2.77 | 45.41 | 0.06x |
| klieber2017q-080-20-t1.qcir | UNSAT | 2.72 | 20.49 | 0.13x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | UNSAT | 0.30 | 1.51 | 0.20x |
| reachqu_query64_1344.qcir | SAT | 12.63 | 47.88 | 0.26x |
| jctc10-fail.qcir | UNSAT | 5.08 | 11.83 | 0.43x |
| jctc2-pass.qcir | SAT | 2.06 | 4.13 | 0.50x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 1.61 | 3.22 | 0.50x |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | SAT | 9.01 | 16.42 | 0.55x |
| klieber2017q-064-16-t1.qcir | UNSAT | 26.27 | 44.56 | 0.59x |
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | SAT | 23.51 | 39.77 | 0.59x |

## M1-r3-default-s2 relative to baseline-c96-default-t60-s1 (134 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **1.15x**.

Top 10 speedups:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-default-s2 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 16.16 | 0.23 | 71.49x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 3.27 | 0.55 | 5.94x |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | SAT | 6.54 | 1.81 | 3.61x |
| robot_grid6_1.tlsf.qcir | SAT | 7.19 | 2.21 | 3.25x |
| DW-sat-09-26-1.qcir | SAT | 3.83 | 1.41 | 2.71x |
| hadw7-8.qcir | UNSAT | 0.27 | 0.09 | 2.67x |
| klieber2017q-082-20-t1.qcir | UNSAT | 34.99 | 13.84 | 2.53x |
| hadw9-10.qcir | UNSAT | 1.92 | 0.88 | 2.18x |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | SAT | 8.30 | 3.82 | 2.17x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | UNSAT | 1.46 | 0.69 | 2.11x |

Top 10 regressions:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-default-s2 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-088-22-t1.qcir | UNSAT | 10.79 | 45.85 | 0.24x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.26 | 0.81 | 0.32x |
| klieber2017q-084-21-t1.qcir | UNSAT | 2.77 | 8.56 | 0.32x |
| klieber2017q-080-20-t1.qcir | UNSAT | 2.72 | 7.75 | 0.35x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 1.61 | 3.28 | 0.49x |
| test_5_5_tic.pg-9.qcir | SAT | 0.41 | 0.78 | 0.52x |
| test_5_5_domino.pg-13.qcir | SAT | 2.56 | 4.78 | 0.54x |
| 10.2.qcir | UNSAT | 1.66 | 2.92 | 0.57x |
| jctc10-fail.qcir | UNSAT | 5.08 | 8.75 | 0.58x |
| chess_solving_mate_in_4_2001_UKR-CH_13.qcir | SAT | 23.51 | 40.19 | 0.58x |

## M1-r3-default-s3 relative to baseline-c96-default-t60-s1 (134 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **1.11x**.

Top 10 speedups:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-default-s3 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-082-20-t1.qcir | UNSAT | 34.99 | 1.16 | 30.19x |
| reachqu_query64_1344.qcir | SAT | 12.63 | 1.76 | 7.18x |
| klieber2017q-074-18-t1.qcir | UNSAT | 39.62 | 8.11 | 4.89x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 1.46 | 0.33 | 4.46x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 1.61 | 0.39 | 4.11x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 6.44 | 1.61 | 4.00x |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | SAT | 9.01 | 2.31 | 3.89x |
| DW-unsat-09-23-1.qcir | UNSAT | 31.35 | 9.16 | 3.42x |
| bt-2x4_13.ig.qcir | UNSAT | 0.71 | 0.22 | 3.31x |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | SAT | 0.77 | 0.25 | 3.10x |

Top 10 regressions:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-default-s3 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-080-20-t1.qcir | UNSAT | 2.72 | 40.82 | 0.07x |
| klieber2017q-084-21-t1.qcir | UNSAT | 2.77 | 33.25 | 0.08x |
| klieber2017q-088-22-t1.qcir | UNSAT | 10.79 | 49.13 | 0.22x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 4.78 | 14.24 | 0.34x |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | SAT | 8.30 | 22.95 | 0.36x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.26 | 0.65 | 0.39x |
| ci.e#1.a#3.E#40.A#60.c#432.w#2.s#8.asp.qcir | UNSAT | 0.07 | 0.25 | 0.40x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.26 | 0.60 | 0.43x |
| test_5_5_domino.pg-13.qcir | SAT | 2.56 | 5.64 | 0.45x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | UNSAT | 0.30 | 0.60 | 0.49x |

## M1-r3-dl-s1 relative to baseline-c96-default-t60-s1 (125 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.91x**.

Top 10 speedups:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-dl-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 16.16 | 0.07 | 161.57x |
| test_5_5_Z.pg-7.qcir | UNSAT | 10.97 | 0.04 | 109.75x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 6.44 | 0.04 | 64.44x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 0.03 | 20.12x |
| klieber2017q-070-17-t1.qcir | UNSAT | 14.14 | 0.99 | 14.34x |
| klieber2017q-072-18-t1.qcir | UNSAT | 34.70 | 2.52 | 13.80x |
| DW-unsat-09-23-1.qcir | UNSAT | 31.35 | 2.37 | 13.25x |
| klieber2017q-074-18-t1.qcir | UNSAT | 39.62 | 4.93 | 8.04x |
| klieber2017q-060-15-eq.qcir | SAT | 14.30 | 2.06 | 6.93x |
| klieber2017q-068-17-t1.qcir | UNSAT | 41.38 | 6.19 | 6.68x |

Top 10 regressions:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-dl-s1 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.25 | 9.71 | 0.03x |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | SAT | 0.41 | 12.28 | 0.03x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.53 | 14.74 | 0.04x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.26 | 5.99 | 0.04x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 3.27 | 55.29 | 0.06x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.16 | 18.58 | 0.06x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.26 | 3.92 | 0.07x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.21 | 17.81 | 0.07x |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | SAT | 0.37 | 4.73 | 0.08x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.19 | 2.16 | 0.09x |

## M1-r3-dl-s2 relative to baseline-c96-default-t60-s1 (126 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.86x**.

Top 10 speedups:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-dl-s2 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_Z.pg-7.qcir | UNSAT | 10.97 | 0.04 | 109.75x |
| jctc8-pass.qcir | SAT | 16.16 | 0.15 | 104.24x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 6.44 | 0.03 | 64.44x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 0.03 | 20.12x |
| DW-unsat-09-23-1.qcir | UNSAT | 31.35 | 3.02 | 10.40x |
| DW-unsat-10-25-1.qcir | UNSAT | 51.65 | 6.54 | 7.90x |
| hadw5-7.qcir | UNSAT | 12.43 | 1.76 | 7.05x |
| DW-unsat-09-22-1.qcir | UNSAT | 18.02 | 2.62 | 6.89x |
| klieber2017q-074-18-t1.qcir | UNSAT | 39.62 | 6.14 | 6.45x |
| klieber2017q-078-19-t1.qcir | UNSAT | 49.71 | 7.95 | 6.25x |

Top 10 regressions:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-dl-s2 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.19 | 5.74 | 0.03x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.53 | 14.60 | 0.04x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.26 | 6.49 | 0.04x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.54 | 12.93 | 0.04x |
| jctc4-fail.qcir | UNSAT | 0.17 | 3.72 | 0.04x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.21 | 17.82 | 0.07x |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | SAT | 0.37 | 4.53 | 0.08x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.93 | 11.48 | 0.08x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.26 | 2.92 | 0.09x |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | SAT | 0.53 | 5.79 | 0.09x |

## M1-r3-dl-s3 relative to baseline-c96-default-t60-s1 (123 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.90x**.

Top 10 speedups:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-dl-s3 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_Z.pg-7.qcir | UNSAT | 10.97 | 0.04 | 109.75x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 6.44 | 0.04 | 64.44x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 0.03 | 20.12x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 1.61 | 0.13 | 12.50x |
| klieber2017q-064-16-eq.qcir | SAT | 19.58 | 2.16 | 9.05x |
| DW-unsat-09-22-1.qcir | UNSAT | 18.02 | 2.21 | 8.14x |
| klieber2017q-074-18-t1.qcir | UNSAT | 39.62 | 4.98 | 7.96x |
| hadw5-7.qcir | UNSAT | 12.43 | 1.81 | 6.88x |
| klieber2017q-078-19-t1.qcir | UNSAT | 49.71 | 10.17 | 4.89x |
| test_5_5_elly.pg-7.qcir | SAT | 0.83 | 0.17 | 4.76x |

Top 10 regressions:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-dl-s3 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.54 | 15.45 | 0.03x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.53 | 13.45 | 0.04x |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | SAT | 0.60 | 12.58 | 0.05x |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | SAT | 0.41 | 8.36 | 0.05x |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | SAT | 0.55 | 8.80 | 0.06x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.16 | 17.37 | 0.07x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.26 | 3.37 | 0.08x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.26 | 2.87 | 0.09x |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | SAT | 0.77 | 8.51 | 0.09x |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | SAT | 0.53 | 5.43 | 0.10x |

## M1-r3-mode1-s1 relative to baseline-c96-default-t60-s1 (111 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.86x**.

Top 10 speedups:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-mode1-s1 s | speedup |
|---|---:|---:|---:|---:|
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | UNSAT | 1.46 | 0.28 | 5.18x |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | SAT | 11.22 | 2.31 | 4.85x |
| hadw2-7.qcir | UNSAT | 18.67 | 4.78 | 3.91x |
| hadw5-7.qcir | UNSAT | 12.43 | 3.58 | 3.47x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 1.61 | 0.54 | 2.99x |
| sc-ungrounded-2x2X2x2_1.qcir | UNSAT | 33.32 | 14.55 | 2.29x |
| sc-ungrounded-2x1X1x3_1.qcir | UNSAT | 3.07 | 1.41 | 2.17x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 1.46 | 0.71 | 2.05x |
| DW-unsat-09-22-1.qcir | UNSAT | 18.02 | 9.16 | 1.97x |
| hadw9-10.qcir | UNSAT | 1.92 | 1.00 | 1.91x |

Top 10 regressions:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-mode1-s1 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_tic.pg-9.qcir | SAT | 0.41 | 10.22 | 0.04x |
| test_5_5_domino.pg-11.qcir | SAT | 0.21 | 4.22 | 0.05x |
| test_5_5_elly.pg-7.qcir | SAT | 0.83 | 10.67 | 0.08x |
| bt2nd-2x5_10.ig.qcir | SAT | 4.88 | 42.42 | 0.12x |
| jctc4-fail.qcir | UNSAT | 0.17 | 0.88 | 0.19x |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | SAT | 8.30 | 36.84 | 0.23x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 4.78 | 19.73 | 0.24x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 7.25 | 0.28x |
| jctc2-pass.qcir | SAT | 2.06 | 6.59 | 0.31x |
| jctc13-fail.qcir | UNSAT | 0.07 | 0.30 | 0.33x |

## M1-r3-mode2-s1 relative to baseline-c96-default-t60-s1 (119 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.91x**.

Top 10 speedups:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-mode2-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 16.16 | 0.20 | 82.02x |
| klieber2017q-082-20-t1.qcir | UNSAT | 34.99 | 2.97 | 11.79x |
| 5.2-1.qcir | SAT | 53.23 | 5.63 | 9.46x |
| hadw2-7.qcir | UNSAT | 18.67 | 2.27 | 8.23x |
| DW-sat-08-22-1.qcir | SAT | 2.01 | 0.29 | 6.85x |
| klieber2017q-072-18-t1.qcir | UNSAT | 34.70 | 6.49 | 5.34x |
| klieber2017q-078-19-t1.qcir | UNSAT | 49.71 | 9.47 | 5.25x |
| klieber2017q-084-21-t1.qcir | UNSAT | 2.77 | 0.53 | 5.23x |
| DW-sat-09-26-1.qcir | SAT | 3.83 | 0.86 | 4.45x |
| klieber2017q-064-16-t1.qcir | UNSAT | 26.27 | 8.90 | 2.95x |

Top 10 regressions:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-mode2-s1 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_tic.pg-9.qcir | SAT | 0.41 | 6.64 | 0.06x |
| test_5_5_domino.pg-11.qcir | SAT | 0.21 | 3.17 | 0.07x |
| jctc4-fail.qcir | UNSAT | 0.17 | 2.16 | 0.08x |
| klieber2017q-080-20-t1.qcir | UNSAT | 2.72 | 26.90 | 0.10x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 10.92 | 0.18x |
| ltl2dba_beta6.tlsf.qcir | SAT | 10.97 | 54.40 | 0.20x |
| test_5_5_skinny.pg-7.qcir | UNSAT | 0.68 | 3.17 | 0.21x |
| test_5_5_knobby.pg-7.qcir | SAT | 4.73 | 21.95 | 0.22x |
| sc-ungrounded-1x2X2x2_2.qcir | UNSAT | 6.95 | 27.96 | 0.25x |
| test_5_5_fatty.pg-7.qcir | UNSAT | 0.44 | 1.71 | 0.26x |

## M1-r3-ccmin3-s1 relative to baseline-c96-default-t60-s1 (139 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **1.12x**.

Top 10 speedups:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-ccmin3-s1 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 49.71 | 1.41 | 35.26x |
| test_5_5_knobby.pg-7.qcir | SAT | 4.73 | 0.79 | 5.97x |
| reachqu_query64_1344.qcir | SAT | 12.63 | 3.22 | 3.92x |
| klieber2017q-082-20-t1.qcir | UNSAT | 34.99 | 9.57 | 3.66x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 1.46 | 0.41 | 3.56x |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | SAT | 5.03 | 1.71 | 2.94x |
| robot_grid6_1.tlsf.qcir | SAT | 7.19 | 2.56 | 2.81x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.93 | 0.35 | 2.68x |
| klieber2017q-108-27-t1.qcir | UNSAT | 32.54 | 12.74 | 2.55x |
| DW-sat-08-23-1.qcir | SAT | 1.76 | 0.69 | 2.54x |

Top 10 regressions:

| instance | result | baseline-c96-default-t60-s1 s | M1-r3-ccmin3-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc10-fail.qcir | UNSAT | 5.08 | 55.62 | 0.09x |
| klieber2017q-084-21-t1.qcir | UNSAT | 2.77 | 14.55 | 0.19x |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | SAT | 6.94 | 24.01 | 0.29x |
| klieber2017q-080-20-t1.qcir | UNSAT | 2.72 | 8.96 | 0.30x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.25 | 0.77 | 0.32x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.26 | 0.70 | 0.37x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 4.78 | 11.42 | 0.42x |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | SAT | 8.30 | 17.72 | 0.47x |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | SAT | 6.19 | 12.19 | 0.51x |
| test_5_5_domino.pg-13.qcir | SAT | 2.56 | 4.73 | 0.54x |

## baseline-t180 relative to baseline-c96-default-t60-s1 (140 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.96x**.

Top 10 speedups:

| instance | result | baseline-c96-default-t60-s1 s | baseline-t180 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 16.16 | 0.15 | 110.66x |
| klieber2017q-078-19-t1.qcir | UNSAT | 49.71 | 10.03 | 4.96x |
| klieber2017q-082-20-t1.qcir | UNSAT | 34.99 | 8.73 | 4.01x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 1.46 | 0.38 | 3.86x |
| DW-unsat-09-23-1.qcir | UNSAT | 31.35 | 9.59 | 3.27x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 1.61 | 0.53 | 3.04x |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | SAT | 0.50 | 0.23 | 2.19x |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | SAT | 11.22 | 5.27 | 2.13x |
| bt-2x4_13.ig.qcir | UNSAT | 0.71 | 0.34 | 2.11x |
| sc-ungrounded-2x2X2x2_1.qcir | UNSAT | 33.32 | 16.40 | 2.03x |

Top 10 regressions:

| instance | result | baseline-c96-default-t60-s1 s | baseline-t180 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-084-21-t1.qcir | UNSAT | 2.77 | 64.06 | 0.04x |
| klieber2017q-080-20-t1.qcir | UNSAT | 2.72 | 18.76 | 0.14x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | UNSAT | 0.30 | 1.40 | 0.21x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.26 | 0.84 | 0.30x |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | SAT | 6.94 | 20.96 | 0.33x |
| test_5_5_tic.pg-9.qcir | SAT | 0.41 | 1.11 | 0.37x |
| klieber2017q-074-18-eq.qcir | SAT | 24.14 | 59.58 | 0.41x |
| test_5_5_domino.pg-13.qcir | SAT | 2.56 | 6.22 | 0.41x |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | SAT | 8.30 | 19.47 | 0.43x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.26 | 0.56 | 0.46x |

## Proof checking (Lean qlrup-check)

| run | checked | verified | other statuses | check s (sum) | check s (max) | proof MB (sum) | proof MB (max) |
|---|---:|---:|---:|---:|---:|---:|---:|
| baseline-t180 | 115 | 115 | - | 1422.8 | 251.6 | 3682.2 | 227.0 |

## Proof coverage

| run | solved | attempted | accepted | rejected | checker timeout | checker memout | too large | checker error | proof run unfinished | not attempted |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| baseline-c96-default-t60-s1 | 141 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 141 |
| M1-r3-default-s1 | 142 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 142 |
| M1-r3-default-s2 | 145 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 145 |
| M1-r3-default-s3 | 143 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 143 |
| M1-r3-dl-s1 | 149 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 149 |
| M1-r3-dl-s2 | 153 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 153 |
| M1-r3-dl-s3 | 146 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 146 |
| M1-r3-mode1-s1 | 115 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 115 |
| M1-r3-mode2-s1 | 135 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 135 |
| M1-r3-ccmin3-s1 | 147 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 147 |
| baseline-t180 | 167 | 115 | 115 | 0 | 0 | 0 | 0 | 0 | 0 | 52 |

- `baseline-c96-default-t60-s1`, not attempted (proofs not requested) (141): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-4.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir` ...
- `M1-r3-default-s1`, not attempted (proofs not requested) (142): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-06-4.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-2x5_17.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir` ...
- `M1-r3-default-s2`, not attempted (proofs not requested) (145): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir` ...
- `M1-r3-default-s3`, not attempted (proofs not requested) (143): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DWs-sat-10-25-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir` ...
- `M1-r3-dl-s1`, not attempted (proofs not requested) (149): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-07-3.qcir`, `CM-sat-07-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir` ...
- `M1-r3-dl-s2`, not attempted (proofs not requested) (153): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-sat-02-01-06-3.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir` ...
- `M1-r3-dl-s3`, not attempted (proofs not requested) (146): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `ci.e#1.a#3.E#40.A#60.c#200.w#6.s#6.asp.qcir` ...
- `M1-r3-mode1-s1`, not attempted (proofs not requested) (115): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir` ...
- `M1-r3-mode2-s1`, not attempted (proofs not requested) (135): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DWs-sat-10-25-1.qcir`, `DWs-unsat-08-17-1.qcir`, `DWs-unsat-08-18-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `bt-2x4_13.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir` ...
- `M1-r3-ccmin3-s1`, not attempted (proofs not requested) (147): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DWs-sat-12-28-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir` ...
- `baseline-t180`, not attempted (solved in more than 20 s) (52): `11.1.qcir`, `3.1.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `9.2.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `bt-2x5_17.ig.qcir`, `bt-3x4_19.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `connect-5x5_9_connect3.ig.qcir`, `connect-6x6_9_connect3.ig.qcir`, `eequery_query42_1344.qcir`, `hadw2-7.qcir`, `hadw5-7.qcir`, `jctc14-unrolled-fail.qcir`, `klieber2017q-064-16-eq.qcir`, `klieber2017q-064-16-t1.qcir`, `klieber2017q-066-16-eq.qcir`, `klieber2017q-068-17-t1.qcir`, `klieber2017q-070-17-eq.qcir`, `klieber2017q-072-18-eq.qcir`, `klieber2017q-072-18-t1.qcir`, `klieber2017q-074-18-eq.qcir`, `klieber2017q-074-18-t1.qcir`, `klieber2017q-076-19-eq.qcir`, `klieber2017q-076-19-t1.qcir`, `klieber2017q-078-19-eq.qcir`, `klieber2017q-084-21-eq.qcir`, `klieber2017q-084-21-t1.qcir`, `klieber2017q-086-21-t1.qcir`, `klieber2017q-088-22-eq.qcir`, `klieber2017q-088-22-t1.qcir`, `klieber2017q-100-25-t1.qcir`, `klieber2017q-108-27-t1.qcir`, `mult9.sat.qcir`, `reachqu_query64_1344.qcir`, `test_5_5_domino.pg-15.qcir`, `test_5_5_el.pg-13.qcir`, `test_5_5_fatty.pg-9.qcir`, `test_5_5_knobby.pg-9.qcir`, `test_5_5_skinny.pg-9.qcir`, `test_5_5_snaky.pg-9.qcir`

