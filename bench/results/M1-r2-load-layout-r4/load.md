# Load measurement M1-r2-load-layout-r4

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 `
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-new`, sha256 59aa524cbd5b4853ec370ef5a5207e5005e23c0d42497fc3281ffbc2f7da94d4, args `--seed=1 `
- cores 0-47, 4 copies of 12 instances, 4 rounds
- order of the arms: A (2026-11-23T04:57:39), B (2026-11-23T04:58:12), A (2026-11-23T04:58:42), B (2026-11-23T04:59:15), A (2026-11-23T04:59:44), B (2026-11-23T05:00:17), A (2026-11-23T05:00:47), B (2026-11-23T05:01:19)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.97 | 2.24 | 1.137 | 1.88-3.66 | 1.57-3.33 | yes |
| DW-unsat-09-22-1.qcir | 10.00 | 9.86 | 0.986 | 8.55-11.36 | 8.12-11.29 | yes |
| jctc10-fail.qcir | 7.33 | 7.96 | 1.085 | 6.30-8.44 | 5.93-9.43 | yes |
| DW-sat-09-26-1.qcir | 3.74 | 3.22 | 0.861 | 3.20-4.17 | 2.89-3.47 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 10.09 | 9.69 | 0.960 | 8.65-10.75 | 8.49-11.10 | yes |
| 9.2.qcir | 13.76 | 12.55 | 0.912 | 12.57-15.03 | 11.69-13.37 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 12.38 | 11.66 | 0.942 | 11.06-13.71 | 10.55-12.58 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 8.53 | 7.93 | 0.930 | 7.23-10.02 | 7.06-8.57 | yes |
| 4.1.qcir | 8.28 | 7.24 | 0.875 | 8.00-8.69 | 7.03-7.64 | yes |
| 5.2-1.qcir | 31.74 | 28.18 | 0.888 | 30.80-32.68 | 27.41-28.98 | yes |
| hadw11-12.qcir | 6.31 | 5.47 | 0.866 | 6.04-6.64 | 5.07-6.01 | yes |
| ltl2dba_beta6.tlsf.qcir | 12.45 | 10.84 | 0.871 | 11.34-13.77 | 10.03-12.03 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **0.939** |  |  |  |

