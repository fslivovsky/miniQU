# Load measurement M1-r2-load-growth-dl

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -dl`
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final3`, sha256 d690db6523e7dd5f19d908dd7777996509bf7d9988e27299469c4f95a28a440d, args `--seed=1 -dl`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T08:11:23), B (2026-11-23T08:16:24), A (2026-11-23T08:21:24), B (2026-11-23T08:26:25), A (2026-11-23T08:31:25), B (2026-11-23T08:36:26)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 9.76 | 6.60 | 0.676 | 8.30-12.53 | 6.44-6.94 | yes |
| DW-unsat-09-22-1.qcir | 7.23 | 2.46 | 0.340 | 5.15-8.05 | 2.28-2.72 | different search |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 22.32 | 14.19 | 0.636 | 19.78-23.10 | 13.67-14.73 | different search |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | - | - | - | - | - | unfinished |
| 9.2.qcir | 18.12 | 12.52 | 0.691 | 17.75-18.77 | 11.90-12.96 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | - | - | - | - | - | unfinished |
| 4.1.qcir | 6.67 | 5.12 | 0.768 | 6.45-7.05 | 4.79-5.46 | yes |
| 5.2-1.qcir | 15.49 | 14.16 | 0.914 | 15.16-15.96 | 14.06-14.32 | yes |
| hadw11-12.qcir | - | - | - | - | - | unfinished |
| ltl2dba_beta6.tlsf.qcir | 16.17 | 14.23 | 0.880 | 15.40-17.08 | 13.57-14.78 | yes |
| **geometric mean** (n=5 identical searches) |  |  | **0.780** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir, chess_solving_mate_in_3_2003_UKR-CH_04.qcir, chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir, chess_solving_mate_in_3_1991_WCSC-15_05.qcir, hadw11-12.qcir

