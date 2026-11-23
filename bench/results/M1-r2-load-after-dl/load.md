# Load measurement M1-r2-load-after-dl

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -dl`
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final5`, sha256 dfbd0f64976b470e04e8a674e9731536b944d4087bbf27019af3987d1add8900, args `--seed=1 -dl`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T09:39:49), B (2026-11-23T09:44:49), A (2026-11-23T09:49:50), B (2026-11-23T09:54:51), A (2026-11-23T09:59:51), B (2026-11-23T10:04:52)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 9.73 | 6.61 | 0.679 | 8.66-11.27 | 6.41-6.86 | yes |
| DW-unsat-09-22-1.qcir | 6.72 | 2.46 | 0.367 | 4.63-8.68 | 2.26-2.71 | different search |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 22.04 | 14.09 | 0.639 | 20.69-24.01 | 13.49-14.59 | different search |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | - | - | - | - | - | unfinished |
| 9.2.qcir | 17.90 | 12.30 | 0.687 | 17.42-18.40 | 11.87-12.60 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | - | - | - | - | - | unfinished |
| 4.1.qcir | 6.62 | 5.07 | 0.767 | 6.45-6.82 | 4.79-5.33 | yes |
| 5.2-1.qcir | 15.55 | 14.14 | 0.909 | 15.39-15.90 | 14.00-14.33 | yes |
| hadw11-12.qcir | - | - | - | - | - | unfinished |
| ltl2dba_beta6.tlsf.qcir | 16.66 | 14.16 | 0.850 | 15.34-18.07 | 13.07-14.60 | yes |
| **geometric mean** (n=5 identical searches) |  |  | **0.773** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir, chess_solving_mate_in_3_2003_UKR-CH_04.qcir, chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir, chess_solving_mate_in_3_1991_WCSC-15_05.qcir, hadw11-12.qcir

