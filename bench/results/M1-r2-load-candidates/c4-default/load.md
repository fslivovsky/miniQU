# Load measurement c4-default

- A (miniQU-final3): `/home/ec2-user/miniqu-work/r2t2/miniQU-final3`, sha256 d690db6523e7dd5f19d908dd7777996509bf7d9988e27299469c4f95a28a440d, args `--seed=1 `
- B (miniQU-c4): `/home/ec2-user/miniqu-work/r2t2/miniQU-c4`, sha256 a286f3b4161e8d01852b7881565875195058263c6037c2b29a4a756646f0760d, args `--seed=1 `
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T09:29:14), B (2026-11-23T09:29:43), A (2026-11-23T09:30:12), B (2026-11-23T09:30:41), A (2026-11-23T09:31:10), B (2026-11-23T09:31:40)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.58 | 1.66 | 1.054 | 1.53-1.67 | 1.47-3.14 | yes |
| DW-unsat-09-22-1.qcir | 6.68 | 8.76 | 1.310 | 6.42-6.97 | 8.13-10.56 | yes |
| jctc10-fail.qcir | 6.08 | 7.23 | 1.189 | 5.03-7.12 | 5.05-8.35 | yes |
| DW-sat-09-26-1.qcir | 2.21 | 3.06 | 1.383 | 2.00-2.41 | 2.78-3.32 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.38 | 9.19 | 0.980 | 8.80-9.83 | 8.17-10.04 | yes |
| 9.2.qcir | 10.70 | 12.38 | 1.157 | 10.06-11.52 | 11.40-13.23 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 11.44 | 11.50 | 1.005 | 10.77-12.06 | 10.23-12.45 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 7.75 | 7.60 | 0.981 | 7.51-8.59 | 6.79-8.56 | yes |
| 4.1.qcir | 6.60 | 7.34 | 1.113 | 6.42-6.97 | 7.13-7.51 | yes |
| 5.2-1.qcir | 28.07 | 28.16 | 1.003 | 27.27-28.89 | 27.15-28.89 | yes |
| hadw11-12.qcir | 5.61 | 5.22 | 0.930 | 5.45-5.76 | 5.02-5.70 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.68 | 10.30 | 0.964 | 10.26-11.22 | 9.77-10.93 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **1.081** |  |  |  |

