# Load measurement c4-mode1

- A (miniQU-final3): `/home/ec2-user/miniqu-work/r2t2/miniQU-final3`, sha256 d690db6523e7dd5f19d908dd7777996509bf7d9988e27299469c4f95a28a440d, args `--seed=1 -mode=1`
- B (miniQU-c4): `/home/ec2-user/miniqu-work/r2t2/miniQU-c4`, sha256 a286f3b4161e8d01852b7881565875195058263c6037c2b29a4a756646f0760d, args `--seed=1 -mode=1`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T09:23:10), B (2026-11-23T09:24:11), A (2026-11-23T09:25:11), B (2026-11-23T09:26:12), A (2026-11-23T09:27:12), B (2026-11-23T09:28:13)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.37 | 1.50 | 1.094 | 1.29-1.46 | 1.26-2.20 | yes |
| DW-unsat-09-22-1.qcir | 6.82 | 9.62 | 1.411 | 6.25-7.30 | 6.79-10.62 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 4.29 | 6.38 | 1.488 | 3.60-4.86 | 4.15-6.94 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 25.87 | 26.04 | 1.006 | 25.45-26.25 | 24.59-26.96 | yes |
| 9.2.qcir | 11.96 | 14.13 | 1.181 | 11.84-12.27 | 13.35-14.54 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.60 | 2.43 | 0.934 | 2.43-2.83 | 2.14-2.59 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.07 | 10.83 | 0.978 | 10.76-11.33 | 9.30-11.87 | yes |
| 4.1.qcir | 5.58 | 6.01 | 1.078 | 5.45-5.63 | 5.83-6.30 | yes |
| 5.2-1.qcir | 17.93 | 17.61 | 0.982 | 17.39-18.53 | 17.06-18.42 | yes |
| hadw11-12.qcir | 7.62 | 7.06 | 0.926 | 7.49-7.82 | 6.89-7.73 | yes |
| ltl2dba_beta6.tlsf.qcir | 10.20 | 9.35 | 0.917 | 9.86-10.34 | 9.10-10.28 | yes |
| **geometric mean** (n=11 identical searches) |  |  | **1.076** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir

