# Load measurement M1-r2-load-before

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1`
- B (new-r1): `/home/ec2-user/miniqu-work/build/bench-M1-r1/miniQU`, sha256 a48a1a946f470f3d3423a96d85548e839206d1dc7577f0433ecba9cdd75f4b86, args `--seed=1`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T03:33:04), B (2026-11-23T03:33:37), A (2026-11-23T03:34:15), B (2026-11-23T03:34:47), A (2026-11-23T03:35:25), B (2026-11-23T03:35:58)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.99 | 3.86 | 1.941 | 1.91-3.36 | 2.31-4.57 | yes |
| DW-unsat-09-22-1.qcir | 9.48 | 13.22 | 1.394 | 8.07-11.08 | 11.79-14.27 | yes |
| jctc10-fail.qcir | 6.78 | 9.92 | 1.462 | 6.32-8.18 | 9.67-11.72 | yes |
| DW-sat-09-26-1.qcir | 3.85 | 4.39 | 1.142 | 3.47-4.15 | 4.09-4.65 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.99 | 12.22 | 1.222 | 9.21-11.81 | 10.59-13.27 | yes |
| 9.2.qcir | 13.79 | 16.06 | 1.165 | 12.67-15.01 | 15.14-16.80 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 12.52 | 14.49 | 1.157 | 10.93-13.50 | 13.23-16.63 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 8.41 | 9.53 | 1.133 | 7.30-9.57 | 8.47-10.30 | yes |
| 4.1.qcir | 8.28 | 9.22 | 1.114 | 7.90-8.55 | 8.92-9.42 | yes |
| 5.2-1.qcir | 31.66 | 35.70 | 1.128 | 30.80-32.91 | 34.55-36.95 | yes |
| hadw11-12.qcir | 6.23 | 6.64 | 1.065 | 5.98-6.73 | 6.17-7.20 | yes |
| ltl2dba_beta6.tlsf.qcir | 12.31 | 12.53 | 1.018 | 11.50-13.50 | 11.43-13.10 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **1.226** |  |  |  |

