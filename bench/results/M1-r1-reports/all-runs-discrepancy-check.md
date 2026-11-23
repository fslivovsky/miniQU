# Benchmark comparison: M1-r1-ccmin3-s1 vs M1-r1-default-s1 vs M1-r1-default-s2 vs M1-r1-default-s3 vs M1-r1-dl-s1 vs M1-r1-dl-s2 vs M1-r1-dl-s3 vs M1-r1-mode1-s1 vs M1-r1-mode2-s1 vs baseline-c96-ccmin3-t60-s1 vs baseline-c96-default-t60-s1 vs baseline-c96-default-t60-s2 vs baseline-c96-default-t60-s3 vs baseline-c96-dl-t60-s1 vs baseline-c96-dl-t60-s2 vs baseline-c96-dl-t60-s3 vs baseline-c96-mode1-t60-s1 vs baseline-c96-mode2-t60-s1 vs baseline-t180 vs baseline-dl-t180

No result discrepancies, solver errors or proof problems.

376 common instances compared (376 in the union).
**Warning:** timeouts differ between runs: {'M1-r1-ccmin3-s1': 60.0, 'M1-r1-default-s1': 60.0, 'M1-r1-default-s2': 60.0, 'M1-r1-default-s3': 60.0, 'M1-r1-dl-s1': 60.0, 'M1-r1-dl-s2': 60.0, 'M1-r1-dl-s3': 60.0, 'M1-r1-mode1-s1': 60.0, 'M1-r1-mode2-s1': 60.0, 'baseline-c96-ccmin3-t60-s1': 60.0, 'baseline-c96-default-t60-s1': 60.0, 'baseline-c96-default-t60-s2': 60.0, 'baseline-c96-default-t60-s3': 60.0, 'baseline-c96-dl-t60-s1': 60.0, 'baseline-c96-dl-t60-s2': 60.0, 'baseline-c96-dl-t60-s3': 60.0, 'baseline-c96-mode1-t60-s1': 60.0, 'baseline-c96-mode2-t60-s1': 60.0, 'baseline-t180': 180.0, 'baseline-dl-t180': 180.0}

## Summary

| run | SAT | UNSAT | solved | total | PAR2 | wall sum (solved) s | cpu sum (solved) s | max RSS MB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| M1-r1-ccmin3-s1 | 85 | 59 | 144 | 376 | 78.2 | 1561 | 1558 | 8200 |
| M1-r1-default-s1 | 81 | 57 | 138 | 376 | 80.5 | 1718 | 1715 | 8210 |
| M1-r1-default-s2 | 85 | 58 | 143 | 376 | 78.6 | 1592 | 1589 | 8211 |
| M1-r1-default-s3 | 83 | 60 | 143 | 376 | 79.0 | 1742 | 1739 | 8203 |
| M1-r1-dl-s1 | 84 | 64 | 148 | 376 | 77.0 | 1590 | 1587 | 8246 |
| M1-r1-dl-s2 | 86 | 65 | 151 | 376 | 76.2 | 1656 | 1653 | 8247 |
| M1-r1-dl-s3 | 82 | 63 | 145 | 376 | 77.8 | 1526 | 1523 | 8227 |
| M1-r1-mode1-s1 | 70 | 45 | 115 | 376 | 86.3 | 1127 | 1124 | 8200 |
| M1-r1-mode2-s1 | 76 | 58 | 134 | 376 | 81.3 | 1546 | 1543 | 8212 |
| baseline-c96-ccmin3-t60-s1 | 87 | 55 | 142 | 376 | 79.0 | 1636 | 1633 | 8223 |
| baseline-c96-default-t60-s1 | 82 | 59 | 141 | 376 | 79.3 | 1628 | 1625 | 8245 |
| baseline-c96-default-t60-s2 | 86 | 60 | 146 | 376 | 77.9 | 1689 | 1686 | 8286 |
| baseline-c96-default-t60-s3 | 85 | 58 | 143 | 376 | 79.1 | 1798 | 1795 | 8255 |
| baseline-c96-dl-t60-s1 | 84 | 66 | 150 | 376 | 76.4 | 1590 | 1586 | 8230 |
| baseline-c96-dl-t60-s2 | 86 | 67 | 153 | 376 | 75.7 | 1703 | 1700 | 8261 |
| baseline-c96-dl-t60-s3 | 84 | 62 | 146 | 376 | 77.7 | 1632 | 1629 | 8253 |
| baseline-c96-mode1-t60-s1 | 72 | 44 | 116 | 376 | 85.9 | 1080 | 1078 | 8226 |
| baseline-c96-mode2-t60-s1 | 77 | 53 | 130 | 376 | 82.3 | 1413 | 1410 | 8248 |
| baseline-t180 | 100 | 67 | 167 | 376 | 209.9 | 3668 | 3664 | 8262 |
| baseline-dl-t180 | 96 | 72 | 168 | 376 | 208.5 | 3521 | 3495 | 8227 |

| run | git | args | timeout | date |
|---|---:|---:|---:|---:|
| M1-r1-ccmin3-s1 | 00eb7a4 | `-ccmin-mode=3` | 60.0 | 2026-11-23T02:46:10 |
| M1-r1-default-s1 | 00eb7a4 | `` | 60.0 | 2026-11-23T01:09:59 |
| M1-r1-default-s2 | 00eb7a4 | `` | 60.0 | 2026-11-23T01:33:52 |
| M1-r1-default-s3 | 00eb7a4 | `` | 60.0 | 2026-11-23T01:57:44 |
| M1-r1-dl-s1 | 00eb7a4 | `-dl` | 60.0 | 2026-11-23T01:22:04 |
| M1-r1-dl-s2 | 00eb7a4 | `-dl` | 60.0 | 2026-11-23T01:45:54 |
| M1-r1-dl-s3 | 00eb7a4 | `-dl` | 60.0 | 2026-11-23T02:09:46 |
| M1-r1-mode1-s1 | 00eb7a4 | `-mode=1` | 60.0 | 2026-11-23T02:21:44 |
| M1-r1-mode2-s1 | 00eb7a4 | `-mode=2` | 60.0 | 2026-11-23T02:34:06 |
| baseline-c96-ccmin3-t60-s1 | c39005a | `-ccmin-mode=3` | 60.0 | 2026-11-23T02:52:10 |
| baseline-c96-default-t60-s1 | c39005a | `` | 60.0 | 2026-11-23T01:16:03 |
| baseline-c96-default-t60-s2 | c39005a | `` | 60.0 | 2026-11-23T01:39:53 |
| baseline-c96-default-t60-s3 | c39005a | `` | 60.0 | 2026-11-23T02:03:45 |
| baseline-c96-dl-t60-s1 | c39005a | `-dl` | 60.0 | 2026-11-23T01:28:03 |
| baseline-c96-dl-t60-s2 | c39005a | `-dl` | 60.0 | 2026-11-23T01:51:49 |
| baseline-c96-dl-t60-s3 | c39005a | `-dl` | 60.0 | 2026-11-23T02:15:46 |
| baseline-c96-mode1-t60-s1 | c39005a | `-mode=1` | 60.0 | 2026-11-23T02:27:56 |
| baseline-c96-mode2-t60-s1 | c39005a | `-mode=2` | 60.0 | 2026-11-23T02:40:07 |
| baseline-t180 | c39005a | `` | 180.0 | 2026-11-21T16:46:30 |
| baseline-dl-t180 | c39005a | `-dl` | 180.0 | 2026-11-21T17:56:52 |

## Uniquely solved

- **M1-r1-dl-s2** only (1): `SR-sat-02-01-06-3.qcir` (31.1s)
- **M1-r1-mode2-s1** only (2): `hadw2-8.qcir` (58.6s), `hadw3-7.qcir` (48.3s)
- **baseline-c96-default-t60-s3** only (1): `CM-sat-07-01-06-3.qcir` (21.5s)
- **baseline-t180** only (2): `connect-5x5_9_connect3.ig.qcir` (72.1s), `connect-6x6_9_connect3.ig.qcir` (49.2s)
- **baseline-dl-t180** only (3): `DWs-sat-10-23-1.qcir` (171.2s), `hadw7-9.qcir` (165.6s), `jctc5-fail.qcir` (7.5s)


## Per family (solved / total)

| family | n | M1-r1-ccmin3-s1 | M1-r1-default-s1 | M1-r1-default-s2 | M1-r1-default-s3 | M1-r1-dl-s1 | M1-r1-dl-s2 | M1-r1-dl-s3 | M1-r1-mode1-s1 | M1-r1-mode2-s1 | baseline-c96-ccmin3-t60-s1 | baseline-c96-default-t60-s1 | baseline-c96-default-t60-s2 | baseline-c96-default-t60-s3 | baseline-c96-dl-t60-s1 | baseline-c96-dl-t60-s2 | baseline-c96-dl-t60-s3 | baseline-c96-mode1-t60-s1 | baseline-c96-mode2-t60-s1 | baseline-t180 | baseline-dl-t180 | PAR2 M1-r1-ccmin3-s1 | PAR2 M1-r1-default-s1 | PAR2 M1-r1-default-s2 | PAR2 M1-r1-default-s3 | PAR2 M1-r1-dl-s1 | PAR2 M1-r1-dl-s2 | PAR2 M1-r1-dl-s3 | PAR2 M1-r1-mode1-s1 | PAR2 M1-r1-mode2-s1 | PAR2 baseline-c96-ccmin3-t60-s1 | PAR2 baseline-c96-default-t60-s1 | PAR2 baseline-c96-default-t60-s2 | PAR2 baseline-c96-default-t60-s3 | PAR2 baseline-c96-dl-t60-s1 | PAR2 baseline-c96-dl-t60-s2 | PAR2 baseline-c96-dl-t60-s3 | PAR2 baseline-c96-mode1-t60-s1 | PAR2 baseline-c96-mode2-t60-s1 | PAR2 baseline-t180 | PAR2 baseline-dl-t180 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| CM | 7 | 1 | 2 | 1 | 0 | 3 | 2 | 2 | 1 | 1 | 2 | 1 | 1 | 3 | 3 | 1 | 1 | 0 | 1 | 1 | 4 | 104.8 | 93.7 | 103.2 | 120.0 | 84.0 | 94.8 | 88.5 | 103.1 | 103.2 | 89.4 | 103.0 | 107.3 | 75.0 | 81.0 | 107.0 | 103.6 | 120.0 | 108.8 | 318.3 | 170.7 |
| DW | 7 | 5 | 5 | 5 | 6 | 7 | 6 | 7 | 5 | 5 | 5 | 6 | 6 | 6 | 7 | 7 | 6 | 5 | 5 | 7 | 7 | 42.0 | 45.0 | 45.6 | 33.8 | 20.1 | 28.6 | 16.2 | 42.6 | 42.0 | 38.2 | 32.7 | 32.1 | 30.7 | 18.8 | 17.0 | 28.5 | 40.2 | 40.5 | 18.7 | 11.7 |
| DWs | 13 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 3 | 1 | 0 | 0 | 1 | 1 | 0 | 0 | 0 | 3 | 0 | 3 | 110.9 | 120.0 | 120.0 | 112.1 | 120.0 | 120.0 | 120.0 | 120.0 | 98.0 | 110.9 | 120.0 | 120.0 | 111.9 | 113.5 | 120.0 | 120.0 | 120.0 | 97.2 | 360.0 | 305.4 |
| JP | 6 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 1 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 109.6 | 109.3 | 120.0 | 108.7 | 120.0 | 120.0 | 120.0 | 120.0 | 105.7 | 104.0 | 120.0 | 120.0 | 120.0 | 360.0 | 308.9 |
| Lights | 2 | 0 | 0 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 2 | 1 | 1 | 1 | 2 | 2 | 1 | 1 | 1 | 2 | 2 | 120.0 | 120.0 | 80.6 | 74.3 | 72.8 | 78.5 | 75.2 | 120.0 | 75.8 | 58.8 | 86.9 | 78.9 | 73.4 | 37.9 | 44.6 | 67.9 | 89.7 | 73.4 | 59.4 | 46.4 |
| LightsTotal | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| SR | 5 | 0 | 0 | 0 | 0 | 0 | 2 | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | 1 | 0 | 1 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 89.1 | 106.3 | 120.0 | 97.5 | 120.0 | 120.0 | 120.0 | 120.0 | 107.8 | 107.9 | 107.3 | 120.0 | 97.6 | 360.0 | 304.3 |
| Sensor | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| abcg | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| add | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| adder | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| amba | 5 | 2 | 1 | 1 | 1 | 2 | 2 | 1 | 1 | 0 | 2 | 1 | 1 | 1 | 2 | 2 | 2 | 1 | 0 | 2 | 2 | 87.7 | 100.8 | 101.1 | 100.5 | 86.4 | 87.6 | 99.9 | 101.6 | 120.0 | 88.7 | 100.8 | 101.2 | 101.6 | 88.1 | 85.9 | 87.6 | 101.4 | 120.0 | 238.0 | 230.2 |
| arbiter | 6 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 2 | 2 | 83.6 | 84.3 | 85.1 | 85.2 | 84.6 | 84.8 | 85.2 | 85.2 | 120.0 | 84.8 | 84.6 | 84.5 | 85.2 | 83.8 | 84.8 | 83.9 | 85.0 | 120.0 | 244.4 | 244.3 |
| auto | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| bar | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| beemldelec | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| beemskbn | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| bs | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| bt | 12 | 4 | 4 | 5 | 5 | 4 | 4 | 4 | 3 | 3 | 4 | 4 | 5 | 4 | 4 | 4 | 5 | 3 | 3 | 8 | 8 | 84.3 | 85.5 | 80.1 | 77.7 | 83.7 | 83.8 | 83.4 | 93.8 | 91.4 | 84.5 | 84.6 | 79.1 | 84.6 | 83.2 | 83.2 | 75.9 | 92.5 | 92.3 | 159.8 | 160.6 |
| cavlc | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| chess | 40 | 32 | 32 | 32 | 32 | 21 | 21 | 20 | 32 | 30 | 32 | 32 | 32 | 32 | 21 | 21 | 20 | 32 | 31 | 32 | 26 | 29.1 | 28.4 | 27.2 | 28.6 | 62.6 | 61.2 | 64.3 | 30.2 | 33.0 | 28.8 | 27.2 | 27.2 | 27.6 | 61.7 | 60.4 | 63.3 | 29.3 | 31.1 | 75.3 | 140.5 |
| ci | 30 | 5 | 5 | 5 | 5 | 8 | 8 | 8 | 5 | 8 | 5 | 5 | 5 | 5 | 8 | 8 | 8 | 5 | 8 | 5 | 8 | 100.1 | 100.2 | 100.2 | 100.1 | 89.3 | 88.2 | 88.3 | 100.1 | 88.8 | 100.2 | 100.1 | 100.1 | 100.1 | 88.2 | 89.1 | 88.4 | 100.1 | 88.4 | 300.1 | 264.8 |
| collector | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 2.9 | 3.1 | 5.5 | 5.2 | 5.1 | 4.8 | 4.6 | 3.7 | 7.8 | 3.7 | 3.2 | 5.3 | 4.8 | 4.1 | 5.2 | 3.6 | 3.5 | 7.2 | 4.0 | 4.8 |
| connect | 7 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 0 | 4 | 2 | 86.9 | 87.1 | 86.9 | 86.5 | 87.3 | 88.5 | 87.2 | 89.2 | 120.0 | 87.0 | 87.4 | 86.8 | 86.7 | 88.2 | 88.1 | 89.0 | 89.1 | 120.0 | 172.6 | 259.3 |
| cycle | 7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| driver | 6 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| ea | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| eequery | 2 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 73.5 | 79.1 | 81.4 | 77.6 | 68.5 | 69.8 | 72.3 | 72.3 | 65.8 | 75.4 | 75.4 | 73.8 | 74.7 | 68.4 | 71.6 | 68.4 | 71.2 | 64.2 | 199.4 | 188.7 |
| ex | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| finan | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| finding | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 8.7 | 12.7 | 9.5 | 9.4 | 8.9 | 10.0 | 9.5 | 13.5 | 52.0 | 8.3 | 12.3 | 9.5 | 9.3 | 6.4 | 9.2 | 7.8 | 11.7 | 48.4 | 13.2 | 10.3 |
| genbuf | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| hadw | 21 | 8 | 8 | 8 | 8 | 8 | 9 | 7 | 10 | 10 | 8 | 8 | 8 | 8 | 8 | 9 | 7 | 10 | 8 | 8 | 9 | 76.0 | 76.1 | 76.3 | 76.0 | 79.2 | 74.4 | 81.9 | 69.4 | 69.3 | 76.1 | 76.3 | 76.6 | 76.5 | 78.7 | 74.0 | 83.3 | 69.2 | 75.9 | 225.7 | 217.8 |
| i | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| jctc | 13 | 5 | 5 | 7 | 3 | 9 | 9 | 9 | 6 | 4 | 6 | 5 | 7 | 3 | 9 | 10 | 9 | 4 | 4 | 12 | 9 | 76.5 | 76.3 | 58.8 | 92.3 | 39.6 | 39.6 | 40.3 | 72.5 | 83.4 | 69.5 | 75.7 | 59.1 | 92.3 | 38.8 | 33.3 | 40.0 | 83.9 | 83.4 | 32.7 | 114.3 |
| klieber | 26 | 22 | 18 | 19 | 21 | 25 | 26 | 25 | 1 | 22 | 17 | 20 | 21 | 20 | 24 | 26 | 26 | 2 | 20 | 25 | 26 | 39.1 | 61.5 | 51.6 | 46.1 | 15.5 | 14.7 | 18.8 | 116.5 | 37.6 | 60.9 | 49.8 | 44.8 | 55.0 | 20.8 | 14.6 | 16.5 | 112.1 | 43.9 | 63.2 | 16.0 |
| l | 8 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| lift | 2 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 60.7 | 60.7 | 61.0 | 60.6 | 61.0 | 61.2 | 61.0 | 61.1 | 62.2 | 60.8 | 60.7 | 61.0 | 60.6 | 61.1 | 61.4 | 61.0 | 61.2 | 62.4 | 181.2 | 181.3 |
| linux | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| load | 5 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 96.2 | 96.2 | 96.3 | 96.2 | 96.2 | 96.3 | 96.2 | 96.2 | 96.8 | 96.2 | 96.2 | 96.3 | 96.2 | 96.2 | 96.3 | 96.2 | 96.3 | 96.8 | 288.3 | 288.3 |
| ltl | 5 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 1 | 97.5 | 98.4 | 100.6 | 98.2 | 98.9 | 99.2 | 99.4 | 98.0 | 120.0 | 98.4 | 98.2 | 99.5 | 98.1 | 98.9 | 99.5 | 99.1 | 97.8 | 120.0 | 290.0 | 291.6 |
| max | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| mem | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| mult | 9 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 0 | 1 | 1 | 110.0 | 112.6 | 111.6 | 111.9 | 110.9 | 112.6 | 111.7 | 110.8 | 120.0 | 110.1 | 111.0 | 111.2 | 111.6 | 111.3 | 111.3 | 110.7 | 110.3 | 120.0 | 326.4 | 325.5 |
| myciel | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| nreachq | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 1 | 0 | 0 | 120.0 | 120.0 | 0.1 | 120.0 | 120.0 | 0.2 | 120.0 | 120.0 | 0.7 | 120.0 | 120.0 | 0.1 | 120.0 | 120.0 | 0.2 | 120.0 | 120.0 | 0.8 | 360.0 | 360.0 |
| numeric | 26 | 20 | 19 | 21 | 21 | 19 | 19 | 19 | 20 | 21 | 20 | 20 | 21 | 21 | 19 | 19 | 20 | 21 | 21 | 22 | 21 | 35.1 | 37.5 | 30.5 | 31.8 | 37.2 | 37.9 | 38.5 | 34.7 | 32.3 | 33.6 | 34.7 | 29.7 | 31.0 | 37.0 | 37.6 | 35.7 | 31.3 | 31.8 | 66.5 | 81.1 |
| prioritized | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| priority | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| reachqu | 3 | 1 | 1 | 0 | 2 | 1 | 1 | 2 | 1 | 2 | 1 | 1 | 0 | 2 | 1 | 1 | 2 | 1 | 2 | 1 | 1 | 81.2 | 95.8 | 120.0 | 48.5 | 98.5 | 80.9 | 61.3 | 92.7 | 57.5 | 80.5 | 84.2 | 120.0 | 62.6 | 81.8 | 81.4 | 55.4 | 83.3 | 57.2 | 248.9 | 240.2 |
| robot | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 2.7 | 4.9 | 2.4 | 4.8 | 2.3 | 5.2 | 2.3 | 4.0 | 24.2 | 3.3 | 7.2 | 2.5 | 5.8 | 2.6 | 8.1 | 2.4 | 4.5 | 51.1 | 6.4 | 2.0 |
| round | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1.9 | 2.0 | 2.2 | 1.8 | 1.4 | 0.6 | 2.0 | 1.5 | 2.6 | 1.6 | 2.0 | 2.2 | 1.8 | 1.5 | 0.6 | 2.0 | 1.5 | 3.0 | 1.5 | 1.8 |
| router | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| s | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| sc | 9 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 4 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 4 | 5 | 5 | 57.2 | 58.5 | 57.1 | 57.5 | 56.0 | 56.9 | 56.2 | 57.3 | 75.2 | 58.2 | 59.7 | 58.8 | 58.4 | 56.2 | 56.9 | 57.0 | 58.2 | 77.2 | 164.2 | 166.0 |
| simple | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| square | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| stay | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| test | 28 | 20 | 20 | 19 | 19 | 21 | 21 | 20 | 12 | 10 | 19 | 19 | 19 | 18 | 20 | 22 | 20 | 13 | 10 | 22 | 22 | 41.7 | 41.8 | 45.8 | 45.7 | 36.1 | 35.6 | 40.1 | 70.8 | 79.0 | 45.5 | 46.2 | 46.5 | 48.8 | 39.1 | 33.1 | 42.2 | 68.6 | 79.6 | 97.7 | 89.1 |
| voter | 2 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 66.1 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 66.4 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |
| workstation | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 120.0 | 360.0 | 360.0 |

## M1-r1-default-s1 relative to M1-r1-ccmin3-s1 (134 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.85x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-default-s1 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | SAT | 26.29 | 7.95 | 3.31x |
| test_5_5_domino.pg-13.qcir | SAT | 4.73 | 1.51 | 3.13x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.63 | 0.23 | 2.78x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.55 | 0.23 | 2.43x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 13.19 | 5.54 | 2.38x |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | SAT | 13.54 | 6.19 | 2.19x |
| test_5_5_knobby.pg-9.qcir | SAT | 52.56 | 26.96 | 1.95x |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | SAT | 0.98 | 0.52 | 1.89x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.57 | 0.31 | 1.87x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.90 | 0.49 | 1.85x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-default-s1 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 54.10 | 0.03x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 47.35 | 0.07x |
| klieber2017q-082-20-t1.qcir | UNSAT | 9.72 | 54.81 | 0.18x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 0.64 | 3.17 | 0.20x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | UNSAT | 0.31 | 1.46 | 0.21x |
| CM-sat-04-01-06-3.qcir | SAT | 13.84 | 54.76 | 0.25x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 3.02 | 0.26x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.50 | 1.81 | 0.27x |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | SAT | 1.76 | 5.89 | 0.30x |
| klieber2017q-064-16-t1.qcir | UNSAT | 14.21 | 47.04 | 0.30x |

## M1-r1-default-s2 relative to M1-r1-ccmin3-s1 (136 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.99x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-default-s2 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 26.45 | 0.24 | 112.08x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 4.13 | 0.66 | 6.25x |
| CM-sat-04-01-06-3.qcir | SAT | 13.84 | 2.62 | 5.28x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 13.19 | 3.72 | 3.55x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.63 | 0.18 | 3.40x |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | SAT | 33.79 | 10.51 | 3.21x |
| DW-sat-09-26-1.qcir | SAT | 4.58 | 1.61 | 2.85x |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | SAT | 26.29 | 9.31 | 2.82x |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | SAT | 18.98 | 6.79 | 2.79x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.76 | 0.79 | 2.23x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-default-s2 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 47.10 | 0.03x |
| jctc6-pass.qcir | SAT | 1.86 | 17.57 | 0.11x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 6.04 | 0.13x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 0.64 | 3.42 | 0.19x |
| klieber2017q-088-22-t1.qcir | UNSAT | 12.75 | 47.55 | 0.27x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.39 | 1.26 | 0.31x |
| ltl2dba_beta6.tlsf.qcir | SAT | 7.70 | 23.11 | 0.33x |
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 0.29 | 0.35x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.50 | 1.26 | 0.40x |
| DW-sat-08-23-1.qcir | SAT | 1.35 | 3.22 | 0.42x |

## M1-r1-default-s3 relative to M1-r1-ccmin3-s1 (135 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.94x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-default-s3 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-082-20-t1.qcir | UNSAT | 9.72 | 1.21 | 8.04x |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | SAT | 18.07 | 2.77 | 6.53x |
| klieber2017q-074-18-t1.qcir | UNSAT | 37.33 | 8.26 | 4.52x |
| bt-2x4_13.ig.qcir | UNSAT | 0.89 | 0.22 | 4.06x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 4.99 | 1.61 | 3.09x |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | SAT | 0.78 | 0.29 | 2.73x |
| chess_solving_mate_in_2_2011_ISC-7B_01.qcir | SAT | 0.86 | 0.37 | 2.35x |
| 5.2-1.qcir | SAT | 47.32 | 22.65 | 2.09x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 1.86 | 1.89x |
| connect-4x4_9_connect3.ig.qcir | SAT | 6.94 | 3.87 | 1.79x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-default-s3 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 50.45 | 0.03x |
| klieber2017q-080-20-t1.qcir | UNSAT | 9.07 | 40.28 | 0.23x |
| klieber2017q-088-22-t1.qcir | UNSAT | 12.75 | 51.26 | 0.25x |
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 0.34 | 0.29x |
| test_5_5_elly.pg-7.qcir | SAT | 0.43 | 1.31 | 0.33x |
| test_5_5_elly.pg-9.qcir | SAT | 3.42 | 8.61 | 0.40x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 1.86 | 0.43x |
| DW-sat-09-26-1.qcir | SAT | 4.58 | 10.36 | 0.44x |
| DW-sat-08-22-1.qcir | SAT | 1.96 | 4.28 | 0.46x |
| klieber2017q-084-21-t1.qcir | UNSAT | 15.26 | 32.79 | 0.47x |

## M1-r1-dl-s1 relative to M1-r1-ccmin3-s1 (130 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.77x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-dl-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 26.45 | 0.08 | 264.50x |
| test_5_5_Z.pg-7.qcir | UNSAT | 6.39 | 0.04 | 63.94x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 4.99 | 0.04 | 49.87x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 0.03 | 20.12x |
| klieber2017q-070-17-t1.qcir | UNSAT | 11.87 | 1.00 | 11.92x |
| klieber2017q-072-18-t1.qcir | UNSAT | 26.33 | 2.57 | 10.26x |
| klieber2017q-074-18-t1.qcir | UNSAT | 37.33 | 4.99 | 7.49x |
| jctc2-pass.qcir | SAT | 5.79 | 0.83 | 6.94x |
| DW-unsat-09-23-1.qcir | UNSAT | 23.60 | 3.48 | 6.79x |
| klieber2017q-100-25-t1.qcir | UNSAT | 58.76 | 9.47 | 6.21x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-dl-s1 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.39 | 12.68 | 0.03x |
| hadw10-11.qcir | UNSAT | 1.81 | 53.74 | 0.03x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.90 | 19.33 | 0.05x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.63 | 13.13 | 0.05x |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | SAT | 0.52 | 9.77 | 0.05x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.16 | 18.62 | 0.06x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 55.50 | 0.06x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.17 | 2.51 | 0.07x |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | SAT | 0.44 | 6.14 | 0.07x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.62 | 8.30 | 0.07x |

## M1-r1-dl-s2 relative to M1-r1-ccmin3-s1 (131 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.73x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-dl-s2 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 26.45 | 0.14 | 182.41x |
| test_5_5_Z.pg-7.qcir | UNSAT | 6.39 | 0.04 | 63.94x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 4.99 | 0.03 | 49.87x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 0.03 | 20.12x |
| DW-unsat-09-23-1.qcir | UNSAT | 23.60 | 3.22 | 7.33x |
| DW-unsat-09-22-1.qcir | UNSAT | 22.43 | 3.37 | 6.66x |
| klieber2017q-074-18-t1.qcir | UNSAT | 37.33 | 6.20 | 6.03x |
| klieber2017q-086-21-t1.qcir | UNSAT | 59.42 | 10.47 | 5.67x |
| hadw5-7.qcir | UNSAT | 9.92 | 1.96 | 5.06x |
| klieber2017q-100-25-t1.qcir | UNSAT | 58.76 | 11.68 | 5.03x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-dl-s2 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.39 | 13.59 | 0.03x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.17 | 4.68 | 0.04x |
| jctc4-fail.qcir | UNSAT | 0.14 | 3.72 | 0.04x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.90 | 17.32 | 0.05x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.62 | 11.84 | 0.05x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.16 | 20.69 | 0.06x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.50 | 8.71 | 0.06x |
| chess_solving_mate_in_2_2009_POL-CH-33_01.qcir | SAT | 0.44 | 6.75 | 0.06x |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | SAT | 0.42 | 5.49 | 0.08x |
| hadw10-11.qcir | UNSAT | 1.81 | 21.50 | 0.08x |

## M1-r1-dl-s3 relative to M1-r1-ccmin3-s1 (123 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.79x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-dl-s3 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_Z.pg-7.qcir | UNSAT | 6.39 | 0.04 | 63.94x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 4.99 | 0.04 | 49.87x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 0.03 | 20.12x |
| jctc6-pass.qcir | SAT | 1.86 | 0.06 | 18.63x |
| klieber2017q-086-21-t1.qcir | UNSAT | 59.42 | 6.74 | 8.81x |
| DW-unsat-09-22-1.qcir | UNSAT | 22.43 | 2.57 | 8.73x |
| klieber2017q-074-18-t1.qcir | UNSAT | 37.33 | 5.04 | 7.41x |
| klieber2017q-064-16-eq.qcir | SAT | 15.75 | 2.21 | 7.12x |
| test_5_5_domino.pg-13.qcir | SAT | 4.73 | 0.81 | 5.82x |
| hadw5-7.qcir | UNSAT | 9.92 | 1.76 | 5.63x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-dl-s3 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.62 | 15.21 | 0.04x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.50 | 10.31 | 0.05x |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | SAT | 0.71 | 14.56 | 0.05x |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | SAT | 0.52 | 8.97 | 0.06x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.90 | 14.46 | 0.06x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.39 | 6.04 | 0.06x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.16 | 17.83 | 0.06x |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | SAT | 0.59 | 8.20 | 0.07x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.76 | 23.86 | 0.07x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 44.86 | 0.08x |

## M1-r1-mode1-s1 relative to M1-r1-ccmin3-s1 (112 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.76x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-mode1-s1 s | speedup |
|---|---:|---:|---:|---:|
| CM-sat-04-01-06-3.qcir | SAT | 13.84 | 1.86 | 7.45x |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | SAT | 12.43 | 2.52 | 4.94x |
| hadw2-7.qcir | UNSAT | 15.26 | 4.98 | 3.06x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | UNSAT | 0.80 | 0.27 | 3.02x |
| hadw5-7.qcir | UNSAT | 9.92 | 3.68 | 2.70x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.63 | 0.27 | 2.36x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.76 | 0.83 | 2.12x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.55 | 0.29 | 1.92x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.57 | 0.31 | 1.86x |
| 4.2.qcir | UNSAT | 1.81 | 1.00 | 1.81x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-mode1-s1 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 4.23 | 0.02x |
| test_5_5_elly.pg-7.qcir | SAT | 0.43 | 10.72 | 0.04x |
| test_5_5_tic.pg-9.qcir | SAT | 0.64 | 10.32 | 0.06x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 38.08 | 0.09x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 7.20 | 0.11x |
| bt2nd-2x5_10.ig.qcir | SAT | 6.79 | 43.23 | 0.16x |
| jctc4-fail.qcir | UNSAT | 0.14 | 0.82 | 0.18x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 7.31 | 0.28x |
| connect-3x3_9_connect3.ig.qcir | UNSAT | 1.11 | 3.92 | 0.28x |
| klieber2017q-060-15-eq.qcir | SAT | 8.71 | 30.22 | 0.29x |

## M1-r1-mode2-s1 relative to M1-r1-ccmin3-s1 (117 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.83x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-mode2-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 26.45 | 0.23 | 117.04x |
| klieber2017q-084-21-t1.qcir | UNSAT | 15.26 | 0.54 | 28.32x |
| 5.2-1.qcir | SAT | 47.32 | 6.25 | 7.58x |
| hadw2-7.qcir | UNSAT | 15.26 | 2.36 | 6.46x |
| jctc2-pass.qcir | SAT | 5.79 | 0.94 | 6.13x |
| DW-sat-09-26-1.qcir | SAT | 4.58 | 1.16 | 3.96x |
| klieber2017q-072-18-t1.qcir | UNSAT | 26.33 | 6.69 | 3.94x |
| DW-sat-08-22-1.qcir | SAT | 1.96 | 0.51 | 3.88x |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | SAT | 26.29 | 8.06 | 3.26x |
| klieber2017q-082-20-t1.qcir | UNSAT | 9.72 | 3.07 | 3.17x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | M1-r1-mode2-s1 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 3.22 | 0.03x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 22.16 | 0.04x |
| jctc4-fail.qcir | UNSAT | 0.14 | 2.52 | 0.06x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 49.32 | 0.07x |
| test_5_5_tic.pg-9.qcir | SAT | 0.64 | 6.69 | 0.10x |
| robot_grid6_1.tlsf.qcir | SAT | 2.67 | 24.23 | 0.11x |
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 9.98 | 0.14x |
| sc-ungrounded-1x2X2x2_2.qcir | UNSAT | 4.23 | 29.93 | 0.14x |
| finding_nemo_1.tlsf.qcir | SAT | 8.66 | 51.99 | 0.17x |
| test_5_5_skinny.pg-7.qcir | UNSAT | 0.58 | 3.22 | 0.18x |

## baseline-c96-ccmin3-t60-s1 relative to M1-r1-ccmin3-s1 (136 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.94x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-ccmin3-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-076-19-t1.qcir | UNSAT | 29.91 | 3.72 | 8.04x |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | SAT | 26.29 | 6.39 | 4.11x |
| 5.2-1.qcir | SAT | 47.32 | 12.83 | 3.69x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 13.19 | 3.98 | 3.32x |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | SAT | 18.07 | 5.64 | 3.21x |
| DW-unsat-09-22-1.qcir | UNSAT | 22.43 | 9.82 | 2.28x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 1.61 | 2.19x |
| DW-unsat-09-23-1.qcir | UNSAT | 23.60 | 11.32 | 2.09x |
| klieber2017q-100-25-t1.qcir | UNSAT | 58.76 | 32.90 | 1.79x |
| 4.2.qcir | UNSAT | 1.81 | 1.11 | 1.63x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-ccmin3-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 58.19 | 0.02x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 3.98 | 0.20x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | UNSAT | 0.31 | 1.51 | 0.21x |
| jctc6-pass.qcir | SAT | 1.86 | 8.35 | 0.22x |
| ci.e#1.a#3.E#40.A#60.c#424.w#2.s#1.asp.qcir | UNSAT | 0.14 | 0.41 | 0.34x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 0.64 | 1.46 | 0.44x |
| klieber2017q-070-17-eq.qcir | SAT | 16.36 | 35.92 | 0.46x |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | SAT | 12.43 | 26.47 | 0.47x |
| hadw10-11.qcir | UNSAT | 1.81 | 3.72 | 0.49x |
| test_5_5_elly.pg-7.qcir | SAT | 0.43 | 0.84 | 0.51x |

## baseline-c96-default-t60-s1 relative to M1-r1-ccmin3-s1 (136 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.92x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-default-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-084-21-t1.qcir | UNSAT | 15.26 | 2.77 | 5.52x |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | SAT | 26.29 | 6.94 | 3.79x |
| klieber2017q-080-20-t1.qcir | UNSAT | 9.07 | 2.72 | 3.34x |
| jctc2-pass.qcir | SAT | 5.79 | 2.06 | 2.80x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 13.19 | 4.78 | 2.76x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.63 | 0.25 | 2.56x |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | SAT | 18.98 | 8.30 | 2.29x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.57 | 0.26 | 2.21x |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | SAT | 13.54 | 6.19 | 2.19x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.55 | 0.26 | 2.15x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-default-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 49.71 | 0.03x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 4.73 | 0.17x |
| klieber2017q-082-20-t1.qcir | UNSAT | 9.72 | 34.99 | 0.28x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 12.63 | 0.28x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.50 | 1.46 | 0.34x |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | SAT | 1.76 | 5.03 | 0.35x |
| robot_grid6_1.tlsf.qcir | SAT | 2.67 | 7.19 | 0.37x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 0.64 | 1.61 | 0.40x |
| klieber2017q-108-27-t1.qcir | UNSAT | 12.95 | 32.54 | 0.40x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.39 | 0.93 | 0.41x |

## baseline-c96-default-t60-s2 relative to M1-r1-ccmin3-s1 (138 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **1.03x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-default-t60-s2 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 26.45 | 0.27 | 99.44x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 4.13 | 0.68 | 6.06x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 13.19 | 2.87 | 4.60x |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | SAT | 18.98 | 4.23 | 4.49x |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | SAT | 33.79 | 9.61 | 3.52x |
| klieber2017q-088-22-t1.qcir | UNSAT | 12.75 | 3.77 | 3.38x |
| DW-sat-09-26-1.qcir | SAT | 4.58 | 1.56 | 2.94x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.63 | 0.22 | 2.91x |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | SAT | 26.29 | 9.16 | 2.87x |
| klieber2017q-074-18-t1.qcir | UNSAT | 37.33 | 13.23 | 2.82x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-default-t60-s2 s | speedup |
|---|---:|---:|---:|---:|
| jctc6-pass.qcir | SAT | 1.86 | 22.40 | 0.08x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 4.73 | 0.17x |
| klieber2017q-080-20-t1.qcir | UNSAT | 9.07 | 36.19 | 0.25x |
| klieber2017q-084-21-t1.qcir | UNSAT | 15.26 | 57.37 | 0.27x |
| test_5_5_tippy.pg-9.qcir | SAT | 17.37 | 57.48 | 0.30x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.39 | 1.10 | 0.35x |
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 0.26 | 0.39x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | UNSAT | 0.80 | 1.97 | 0.41x |
| ltl2dba_beta6.tlsf.qcir | SAT | 7.70 | 17.47 | 0.44x |
| CM-sat-04-01-06-3.qcir | SAT | 13.84 | 31.30 | 0.44x |

## baseline-c96-default-t60-s3 relative to M1-r1-ccmin3-s1 (134 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.88x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-default-t60-s3 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | SAT | 18.07 | 2.41 | 7.49x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 4.99 | 1.71 | 2.92x |
| bt-2x4_13.ig.qcir | UNSAT | 0.89 | 0.34 | 2.66x |
| 5.2-1.qcir | SAT | 47.32 | 18.62 | 2.54x |
| chess_solving_mate_in_2_2011_ISC-7B_01.qcir | SAT | 0.86 | 0.36 | 2.42x |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | SAT | 0.78 | 0.33 | 2.39x |
| DW-unsat-09-22-1.qcir | UNSAT | 22.43 | 9.96 | 2.25x |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | SAT | 13.49 | 6.59 | 2.05x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 13.19 | 6.64 | 1.99x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#1.asp.qcir | UNSAT | 0.80 | 0.41 | 1.98x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-default-t60-s3 s | speedup |
|---|---:|---:|---:|---:|
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 15.61 | 0.09x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 27.93 | 0.13x |
| klieber2017q-080-20-t1.qcir | UNSAT | 9.07 | 56.58 | 0.16x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | UNSAT | 0.31 | 1.76 | 0.18x |
| klieber2017q-108-27-t1.qcir | UNSAT | 12.95 | 55.22 | 0.23x |
| klieber2017q-082-20-t1.qcir | UNSAT | 9.72 | 30.38 | 0.32x |
| klieber2017q-084-21-t1.qcir | UNSAT | 15.26 | 47.18 | 0.32x |
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 0.30 | 0.34x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 2.11 | 0.38x |
| test_5_5_elly.pg-9.qcir | SAT | 3.42 | 8.96 | 0.38x |

## baseline-c96-dl-t60-s1 relative to M1-r1-ccmin3-s1 (129 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.79x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-dl-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 26.45 | 0.09 | 264.50x |
| test_5_5_Z.pg-7.qcir | UNSAT | 6.39 | 0.04 | 63.94x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 4.99 | 0.04 | 49.87x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 0.03 | 20.12x |
| klieber2017q-100-25-t1.qcir | UNSAT | 58.76 | 4.33 | 13.58x |
| test_5_5_knobby.pg-9.qcir | SAT | 52.56 | 6.44 | 8.16x |
| DW-unsat-09-23-1.qcir | UNSAT | 23.60 | 3.12 | 7.58x |
| jctc2-pass.qcir | SAT | 5.79 | 0.94 | 6.19x |
| klieber2017q-086-21-t1.qcir | UNSAT | 59.42 | 10.87 | 5.47x |
| klieber2017q-068-17-t1.qcir | UNSAT | 36.53 | 8.06 | 4.53x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-dl-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.39 | 14.56 | 0.03x |
| hadw10-11.qcir | UNSAT | 1.81 | 51.68 | 0.04x |
| chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir | SAT | 0.52 | 9.16 | 0.06x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.63 | 10.77 | 0.06x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.90 | 12.68 | 0.07x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.17 | 2.26 | 0.07x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.62 | 8.40 | 0.07x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.76 | 23.60 | 0.07x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.16 | 15.40 | 0.08x |
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 16.77 | 0.08x |

## baseline-c96-dl-t60-s2 relative to M1-r1-ccmin3-s1 (130 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.78x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-dl-t60-s2 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 26.45 | 0.17 | 160.30x |
| klieber2017q-088-22-t1.qcir | UNSAT | 12.75 | 0.12 | 109.89x |
| test_5_5_Z.pg-7.qcir | UNSAT | 6.39 | 0.04 | 63.94x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 4.99 | 0.04 | 49.87x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 0.03 | 20.12x |
| klieber2017q-074-18-t1.qcir | UNSAT | 37.33 | 2.62 | 14.25x |
| DW-unsat-09-23-1.qcir | UNSAT | 23.60 | 2.71 | 8.70x |
| DW-unsat-09-22-1.qcir | UNSAT | 22.43 | 2.67 | 8.41x |
| klieber2017q-072-18-t1.qcir | UNSAT | 26.33 | 3.37 | 7.80x |
| test_5_5_knobby.pg-9.qcir | SAT | 52.56 | 12.53 | 4.19x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-dl-t60-s2 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.17 | 5.69 | 0.03x |
| jctc4-fail.qcir | UNSAT | 0.14 | 4.28 | 0.03x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.90 | 17.93 | 0.05x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.39 | 6.39 | 0.06x |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | SAT | 0.59 | 9.01 | 0.07x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.16 | 14.75 | 0.08x |
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 17.93 | 0.08x |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | SAT | 0.42 | 5.18 | 0.08x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.62 | 7.70 | 0.08x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.50 | 6.09 | 0.08x |

## baseline-c96-dl-t60-s3 relative to M1-r1-ccmin3-s1 (126 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.77x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-dl-t60-s3 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_Z.pg-7.qcir | UNSAT | 6.39 | 0.04 | 63.94x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 4.99 | 0.04 | 49.87x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 0.03 | 20.12x |
| jctc6-pass.qcir | SAT | 1.86 | 0.06 | 18.63x |
| DW-unsat-09-22-1.qcir | UNSAT | 22.43 | 2.36 | 9.51x |
| klieber2017q-070-17-t1.qcir | UNSAT | 11.87 | 1.46 | 8.13x |
| test_5_5_domino.pg-13.qcir | SAT | 4.73 | 0.59 | 8.02x |
| hadw5-7.qcir | UNSAT | 9.92 | 1.31 | 7.57x |
| jctc8-pass.qcir | SAT | 26.45 | 3.52 | 7.52x |
| klieber2017q-074-18-t1.qcir | UNSAT | 37.33 | 6.24 | 5.98x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-dl-t60-s3 s | speedup |
|---|---:|---:|---:|---:|
| jctc4-fail.qcir | UNSAT | 0.14 | 25.24 | 0.01x |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | SAT | 0.71 | 13.44 | 0.05x |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | SAT | 0.50 | 7.80 | 0.06x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.16 | 17.43 | 0.07x |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | SAT | 0.42 | 5.99 | 0.07x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.39 | 5.13 | 0.08x |
| chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir | SAT | 0.78 | 10.07 | 0.08x |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | SAT | 0.59 | 7.45 | 0.08x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 43.27 | 0.08x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.76 | 19.43 | 0.09x |

## baseline-c96-mode1-t60-s1 relative to M1-r1-ccmin3-s1 (111 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.79x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-mode1-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | SAT | 12.43 | 2.16 | 5.75x |
| hadw5-7.qcir | UNSAT | 9.92 | 3.37 | 2.94x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.63 | 0.25 | 2.56x |
| hadw2-7.qcir | UNSAT | 15.26 | 6.43 | 2.37x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.76 | 0.81 | 2.17x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.57 | 0.29 | 2.00x |
| 4.2.qcir | UNSAT | 1.81 | 0.91 | 1.99x |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | SAT | 0.55 | 0.28 | 1.99x |
| klieber2017q-072-18-eq.qcir | SAT | 39.80 | 20.75 | 1.92x |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | SAT | 0.98 | 0.52 | 1.90x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-mode1-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 10.68 | 0.01x |
| test_5_5_tic.pg-9.qcir | SAT | 0.64 | 12.48 | 0.05x |
| test_5_5_elly.pg-9.qcir | SAT | 3.42 | 46.93 | 0.07x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 9.46 | 0.08x |
| jctc4-fail.qcir | UNSAT | 0.14 | 0.94 | 0.15x |
| 5-5-6-3-3-81-EdAu.qcir | SAT | 0.02 | 0.47 | 0.21x |
| jctc13-fail.qcir | UNSAT | 0.06 | 0.44 | 0.23x |
| bt2nd-2x5_10.ig.qcir | SAT | 6.79 | 27.96 | 0.24x |
| test_5_5_elly.pg-7.qcir | SAT | 0.43 | 1.61 | 0.27x |
| ci.e#1.a#3.E#40.A#60.c#416.w#2.s#3.asp.qcir | UNSAT | 0.64 | 2.16 | 0.30x |

## baseline-c96-mode2-t60-s1 relative to M1-r1-ccmin3-s1 (116 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.73x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-mode2-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| jctc6-pass.qcir | SAT | 1.86 | 0.12 | 16.20x |
| 5.2-1.qcir | SAT | 47.32 | 5.74 | 8.25x |
| jctc2-pass.qcir | SAT | 5.79 | 0.90 | 6.40x |
| DW-sat-08-22-1.qcir | SAT | 1.96 | 0.41 | 4.78x |
| hadw2-7.qcir | UNSAT | 15.26 | 3.32 | 4.59x |
| DW-sat-09-26-1.qcir | SAT | 4.58 | 1.05 | 4.34x |
| klieber2017q-074-18-t1.qcir | UNSAT | 37.33 | 9.97 | 3.74x |
| eequery_query42_1344.qcir | UNSAT | 26.93 | 8.45 | 3.19x |
| DW-sat-08-23-1.qcir | SAT | 1.35 | 0.54 | 2.52x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 13.19 | 5.33 | 2.47x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | baseline-c96-mode2-t60-s1 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 22.55 | 0.04x |
| robot_grid6_1.tlsf.qcir | SAT | 2.67 | 51.09 | 0.05x |
| jctc4-fail.qcir | UNSAT | 0.14 | 2.72 | 0.05x |
| test_5_5_domino.pg-11.qcir | SAT | 0.05 | 1.61 | 0.06x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 47.74 | 0.07x |
| test_5_5_tic.pg-9.qcir | SAT | 0.64 | 8.35 | 0.08x |
| test_5_5_fatty.pg-7.qcir | UNSAT | 0.45 | 3.37 | 0.13x |
| sc-ungrounded-1x2X2x2_2.qcir | UNSAT | 4.23 | 31.12 | 0.14x |
| jctc13-fail.qcir | UNSAT | 0.06 | 0.70 | 0.14x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 13.49 | 0.15x |

## baseline-t180 relative to M1-r1-ccmin3-s1 (143 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.88x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | baseline-t180 s | speedup |
|---|---:|---:|---:|---:|
| jctc8-pass.qcir | SAT | 26.45 | 0.15 | 181.16x |
| jctc6-pass.qcir | SAT | 1.86 | 0.22 | 8.62x |
| jctc2-pass.qcir | SAT | 5.79 | 1.46 | 3.97x |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | SAT | 13.54 | 4.67 | 2.90x |
| chess_solving_mate_in_3_2000_CZE-CH_04.qcir | SAT | 33.79 | 12.29 | 2.75x |
| bt-2x4_13.ig.qcir | UNSAT | 0.89 | 0.34 | 2.63x |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | SAT | 1.76 | 0.68 | 2.61x |
| chess_solving_mate_in_3_1978_WCSC-2_05.qcir | SAT | 13.19 | 5.12 | 2.58x |
| DW-unsat-09-23-1.qcir | UNSAT | 23.60 | 9.59 | 2.46x |
| chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir | SAT | 0.90 | 0.37 | 2.44x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | baseline-t180 s | speedup |
|---|---:|---:|---:|---:|
| reachqu_query64_1344.qcir | SAT | 3.52 | 26.81 | 0.13x |
| klieber2017q-078-19-t1.qcir | UNSAT | 1.41 | 10.03 | 0.14x |
| test_5_5_domino.pg-15.qcir | SAT | 27.19 | 168.39 | 0.16x |
| CM-sat-04-01-06-3.qcir | SAT | 13.84 | 68.20 | 0.20x |
| ci.e#1.a#3.E#40.A#60.c#400.w#2.s#4.asp.qcir | UNSAT | 0.31 | 1.40 | 0.22x |
| klieber2017q-084-21-t1.qcir | UNSAT | 15.26 | 64.06 | 0.24x |
| test_5_5_knobby.pg-7.qcir | SAT | 0.79 | 2.96 | 0.27x |
| test_5_5_elly.pg-9.qcir | SAT | 3.42 | 11.50 | 0.30x |
| klieber2017q-108-27-t1.qcir | UNSAT | 12.95 | 34.25 | 0.38x |
| klieber2017q-078-19-eq.qcir | SAT | 25.59 | 64.90 | 0.39x |

## baseline-dl-t180 relative to M1-r1-ccmin3-s1 (134 instances solved by both)

Geometric-mean speedup (times clamped at 0.1s): **0.66x**.

Top 10 speedups:

| instance | result | M1-r1-ccmin3-s1 s | baseline-dl-t180 s | speedup |
|---|---:|---:|---:|---:|
| test_5_5_Z.pg-7.qcir | UNSAT | 6.39 | 0.10 | 63.94x |
| test_5_5_snaky.pg-7.qcir | UNSAT | 4.99 | 0.06 | 49.87x |
| test_5_5_L.pg-7.qcir | UNSAT | 2.01 | 0.04 | 20.12x |
| jctc6-pass.qcir | SAT | 1.86 | 0.15 | 12.67x |
| reachqu_query64_1344.qcir | SAT | 3.52 | 0.48 | 7.33x |
| klieber2017q-074-18-t1.qcir | UNSAT | 37.33 | 5.77 | 6.47x |
| klieber2017q-100-25-t1.qcir | UNSAT | 58.76 | 10.88 | 5.40x |
| DW-unsat-09-22-1.qcir | UNSAT | 22.43 | 5.17 | 4.34x |
| klieber2017q-068-17-t1.qcir | UNSAT | 36.53 | 8.63 | 4.23x |
| hadw5-7.qcir | UNSAT | 9.92 | 2.65 | 3.74x |

Top 10 regressions:

| instance | result | M1-r1-ccmin3-s1 s | baseline-dl-t180 s | speedup |
|---|---:|---:|---:|---:|
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | SAT | 1.76 | 71.63 | 0.02x |
| chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir | SAT | 0.39 | 14.73 | 0.03x |
| hadw10-11.qcir | UNSAT | 1.81 | 42.79 | 0.04x |
| chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir | SAT | 0.63 | 13.44 | 0.05x |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | SAT | 4.13 | 64.10 | 0.06x |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | SAT | 5.99 | 88.43 | 0.07x |
| chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir | SAT | 0.57 | 8.43 | 0.07x |
| chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir | SAT | 0.17 | 2.31 | 0.07x |
| chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir | SAT | 0.62 | 8.08 | 0.08x |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | SAT | 1.16 | 14.76 | 0.08x |

## Proof checking (Lean qlrup-check)

| run | checked | verified | other statuses | check s (sum) | check s (max) | proof MB (sum) | proof MB (max) |
|---|---:|---:|---:|---:|---:|---:|---:|
| baseline-t180 | 115 | 115 | - | 1422.8 | 251.6 | 3682.2 | 227.0 |

## Proof coverage

| run | solved | attempted | accepted | rejected | checker timeout | checker memout | too large | checker error | proof run unfinished | not attempted |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| M1-r1-ccmin3-s1 | 144 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 144 |
| M1-r1-default-s1 | 138 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 138 |
| M1-r1-default-s2 | 143 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 143 |
| M1-r1-default-s3 | 143 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 143 |
| M1-r1-dl-s1 | 148 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 148 |
| M1-r1-dl-s2 | 151 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 151 |
| M1-r1-dl-s3 | 145 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 145 |
| M1-r1-mode1-s1 | 115 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 115 |
| M1-r1-mode2-s1 | 134 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 134 |
| baseline-c96-ccmin3-t60-s1 | 142 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 142 |
| baseline-c96-default-t60-s1 | 141 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 141 |
| baseline-c96-default-t60-s2 | 146 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 146 |
| baseline-c96-default-t60-s3 | 143 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 143 |
| baseline-c96-dl-t60-s1 | 150 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 150 |
| baseline-c96-dl-t60-s2 | 153 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 153 |
| baseline-c96-dl-t60-s3 | 146 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 146 |
| baseline-c96-mode1-t60-s1 | 116 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 116 |
| baseline-c96-mode2-t60-s1 | 130 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 130 |
| baseline-t180 | 167 | 115 | 115 | 0 | 0 | 0 | 0 | 0 | 0 | 52 |
| baseline-dl-t180 | 168 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 168 |

- `M1-r1-ccmin3-s1`, not attempted (proofs not requested) (144): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DWs-sat-12-28-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir` ...
- `M1-r1-default-s1`, not attempted (proofs not requested) (138): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-06-4.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir`, `chess_solving_mate_in_3_2010_UKR-CH_04.qcir` ...
- `M1-r1-default-s2`, not attempted (proofs not requested) (143): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir` ...
- `M1-r1-default-s3`, not attempted (proofs not requested) (143): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DWs-sat-10-25-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir` ...
- `M1-r1-dl-s1`, not attempted (proofs not requested) (148): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-07-3.qcir`, `CM-sat-07-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir`, `ci.e#1.a#3.E#40.A#60.c#200.w#6.s#6.asp.qcir` ...
- `M1-r1-dl-s2`, not attempted (proofs not requested) (151): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-sat-02-01-06-3.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir` ...
- `M1-r1-dl-s3`, not attempted (proofs not requested) (145): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `ci.e#1.a#3.E#40.A#60.c#200.w#6.s#6.asp.qcir`, `ci.e#1.a#3.E#40.A#60.c#208.w#6.s#8.asp.qcir` ...
- `M1-r1-mode1-s1`, not attempted (proofs not requested) (115): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir`, `chess_solving_mate_in_3_2010_UKR-CH_04.qcir`, `chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir` ...
- `M1-r1-mode2-s1`, not attempted (proofs not requested) (134): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DWs-sat-10-25-1.qcir`, `DWs-unsat-08-17-1.qcir`, `DWs-unsat-08-18-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `bt-2x4_13.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir` ...
- `baseline-c96-ccmin3-t60-s1`, not attempted (proofs not requested) (142): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DWs-sat-12-28-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir` ...
- `baseline-c96-default-t60-s1`, not attempted (proofs not requested) (141): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-4.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir` ...
- `baseline-c96-default-t60-s2`, not attempted (proofs not requested) (146): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir` ...
- `baseline-c96-default-t60-s3`, not attempted (proofs not requested) (143): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `CM-sat-07-01-06-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DWs-sat-10-25-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir` ...
- `baseline-c96-dl-t60-s1`, not attempted (proofs not requested) (150): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `DWs-unsat-08-17-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir` ...
- `baseline-c96-dl-t60-s2`, not attempted (proofs not requested) (153): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir` ...
- `baseline-c96-dl-t60-s3`, not attempted (proofs not requested) (146): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `ci.e#1.a#3.E#40.A#60.c#200.w#6.s#6.asp.qcir`, `ci.e#1.a#3.E#40.A#60.c#208.w#6.s#8.asp.qcir` ...
- `baseline-c96-mode1-t60-s1`, not attempted (proofs not requested) (116): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `amba2c7n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir`, `chess_solving_mate_in_3_2008_ISC-4B_07.qcir`, `chess_solving_mate_in_3_2010_UKR-CH_04.qcir` ...
- `baseline-c96-mode2-t60-s1`, not attempted (proofs not requested) (130): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-4.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DWs-sat-10-25-1.qcir`, `DWs-unsat-08-17-1.qcir`, `DWs-unsat-08-18-1.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `bt-2x4_13.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir`, `chess_solving_mate_in_2_2005_POLTAVA-OPEN_01.qcir`, `chess_solving_mate_in_2_2008_BEL-CH-16B_08.qcir`, `chess_solving_mate_in_2_2009_BEL-CH-17B_01.qcir`, `chess_solving_mate_in_2_2009_POL-CH-33_01.qcir`, `chess_solving_mate_in_2_2011_GBR-CH-32_03.qcir`, `chess_solving_mate_in_2_2011_ISC-7B_01.qcir`, `chess_solving_mate_in_2_2011_ROM-CH-W_02.qcir`, `chess_solving_mate_in_2_2011_WCCC-OPEN-54_01.qcir`, `chess_solving_mate_in_2_2012_GER-CH-36-19_03.qcir`, `chess_solving_mate_in_2_2014_NED-CH-20B_09.qcir`, `chess_solving_mate_in_2_2015_GBR-CH-36_02.qcir`, `chess_solving_mate_in_3_1978_WCSC-2_05.qcir`, `chess_solving_mate_in_3_1991_WCSC-15_05.qcir`, `chess_solving_mate_in_3_2000_CZE-CH_04.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `chess_solving_mate_in_3_2003_UKR-CH_04.qcir` ...
- `baseline-t180`, not attempted (solved in more than 20 s) (52): `11.1.qcir`, `3.1.qcir`, `5.1-1.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `9.2.qcir`, `CM-sat-04-01-06-3.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `bt-2x5_17.ig.qcir`, `bt-3x4_19.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `chess_solving_mate_in_3_2001_UKR-CH_06.qcir`, `connect-5x5_9_connect3.ig.qcir`, `connect-6x6_9_connect3.ig.qcir`, `eequery_query42_1344.qcir`, `hadw2-7.qcir`, `hadw5-7.qcir`, `jctc14-unrolled-fail.qcir`, `klieber2017q-064-16-eq.qcir`, `klieber2017q-064-16-t1.qcir`, `klieber2017q-066-16-eq.qcir`, `klieber2017q-068-17-t1.qcir`, `klieber2017q-070-17-eq.qcir`, `klieber2017q-072-18-eq.qcir`, `klieber2017q-072-18-t1.qcir`, `klieber2017q-074-18-eq.qcir`, `klieber2017q-074-18-t1.qcir`, `klieber2017q-076-19-eq.qcir`, `klieber2017q-076-19-t1.qcir`, `klieber2017q-078-19-eq.qcir`, `klieber2017q-084-21-eq.qcir`, `klieber2017q-084-21-t1.qcir`, `klieber2017q-086-21-t1.qcir`, `klieber2017q-088-22-eq.qcir`, `klieber2017q-088-22-t1.qcir`, `klieber2017q-100-25-t1.qcir`, `klieber2017q-108-27-t1.qcir`, `mult9.sat.qcir`, `reachqu_query64_1344.qcir`, `test_5_5_domino.pg-15.qcir`, `test_5_5_el.pg-13.qcir`, `test_5_5_fatty.pg-9.qcir`, `test_5_5_knobby.pg-9.qcir`, `test_5_5_skinny.pg-9.qcir`, `test_5_5_snaky.pg-9.qcir`
- `baseline-dl-t180`, not attempted (proofs not requested) (168): `1.3.qcir`, `1.4.qcir`, `10.1.qcir`, `10.2.qcir`, `11.1.qcir`, `3.1.qcir`, `3.2.qcir`, `4.1.qcir`, `4.2.qcir`, `5-5-6-10-3-7-EdAd.qcir`, `5-5-6-3-3-81-EdAu.qcir`, `5-5-6-7-3-60-EdAd.qcir`, `5-5-6-8-3-31-EdAd.qcir`, `5-5-6-9-3-20-EdAd.qcir`, `5-5-6-9-3-3-EdAd.qcir`, `5.2-1.qcir`, `5.2-2.qcir`, `8.1.qcir`, `9.1.qcir`, `9.2.qcir`, `9.3.qcir`, `CM-sat-04-01-06-3.qcir`, `CM-sat-04-01-06-4.qcir`, `CM-sat-04-01-07-3.qcir`, `CM-sat-07-01-07-3.qcir`, `DW-sat-08-22-1.qcir`, `DW-sat-08-23-1.qcir`, `DW-sat-09-26-1.qcir`, `DW-unsat-09-22-1.qcir`, `DW-unsat-09-23-1.qcir`, `DW-unsat-10-25-1.qcir`, `DW-unsat-11-26-1.qcir`, `DWs-sat-10-23-1.qcir`, `DWs-unsat-08-17-1.qcir`, `DWs-unsat-08-18-1.qcir`, `JP-unsat-02-06-3.qcir`, `Lights2_0f5381e9.tlsf.qcir`, `Lights2_b02056d6.tlsf.qcir`, `SR-unsat-04-01-08-1.qcir`, `amba2c7n.sat.qcir`, `amba2f9n.sat.qcir`, `arbiter_on_inpchange5.tlsf.qcir`, `arbiter_with_buffer5.tlsf.qcir`, `bt-2x4_13.ig.qcir`, `bt-2x5_17.ig.qcir`, `bt-3x4_19.ig.qcir`, `bt-3x6_9.ig.qcir`, `bt2nd-2x4_8.ig.qcir`, `bt2nd-2x5_10.ig.qcir`, `bt2nd-3x4_12.ig.qcir`, `bt2nd-3x6_10.ig.qcir`, `chess_solving_mate_in_2_1982_WCSC-6_02.qcir`, `chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir`, `chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir`, `chess_solving_mate_in_2_1991_GER-CH-15_01.qcir`, `chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir`, `chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir`, `chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir`, `chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir`, `chess_solving_mate_in_2_2002_WCCC-OPEN-45_01.qcir` ...

