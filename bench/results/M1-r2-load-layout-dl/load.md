# Load measurement M1-r2-load-layout-dl

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -dl`
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-new`, sha256 59aa524cbd5b4853ec370ef5a5207e5005e23c0d42497fc3281ffbc2f7da94d4, args `--seed=1 -dl`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T03:57:05), B (2026-11-23T04:02:05), A (2026-11-23T04:07:06), B (2026-11-23T04:12:07), A (2026-11-23T04:17:07), B (2026-11-23T04:22:08)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 9.68 | 8.20 | 0.847 | 8.32-12.06 | 7.03-10.75 | yes |
| DW-unsat-09-22-1.qcir | 6.86 | 3.51 | 0.512 | 5.05-8.74 | 2.86-4.01 | different search |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 22.22 | 20.21 | 0.910 | 20.55-24.16 | 17.56-21.49 | different search |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | - | - | - | - | - | unfinished |
| 9.2.qcir | 18.09 | 14.94 | 0.826 | 17.30-18.58 | 14.33-15.50 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | - | - | - | - | - | unfinished |
| 4.1.qcir | 6.78 | 5.67 | 0.837 | 6.50-7.00 | 5.61-5.96 | yes |
| 5.2-1.qcir | 15.53 | 13.78 | 0.888 | 15.41-15.69 | 13.57-14.11 | yes |
| hadw11-12.qcir | - | - | - | - | - | unfinished |
| ltl2dba_beta6.tlsf.qcir | 15.73 | 13.38 | 0.851 | 15.16-17.95 | 13.07-14.64 | yes |
| **geometric mean** (n=5 identical searches) |  |  | **0.849** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir, chess_solving_mate_in_3_2003_UKR-CH_04.qcir, chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir, chess_solving_mate_in_3_1991_WCSC-15_05.qcir, hadw11-12.qcir

