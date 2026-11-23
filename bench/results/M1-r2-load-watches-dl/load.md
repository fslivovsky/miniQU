# Load measurement M1-r2-load-watches-dl

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -dl`
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final`, sha256 1b6759f85303591cf63eeefd0aceef65ab3f067da24a9ccf004e058a78aee379, args `--seed=1 -dl`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T06:07:13), B (2026-11-23T06:12:14), A (2026-11-23T06:17:15), B (2026-11-23T06:22:15), A (2026-11-23T06:27:16), B (2026-11-23T06:32:17)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 9.18 | 6.47 | 0.705 | 8.51-10.94 | 6.33-6.64 | yes |
| DW-unsat-09-22-1.qcir | 6.95 | 2.44 | 0.351 | 4.63-8.87 | 2.25-2.71 | different search |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 22.65 | 14.03 | 0.619 | 20.89-24.02 | 13.56-14.30 | different search |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | - | - | - | - | - | unfinished |
| 9.2.qcir | 18.10 | 12.44 | 0.687 | 17.79-18.24 | 11.97-12.63 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | - | - | - | - | - | unfinished |
| 4.1.qcir | 6.62 | 5.07 | 0.766 | 6.37-7.00 | 4.55-5.29 | yes |
| 5.2-1.qcir | 15.55 | 14.07 | 0.904 | 15.32-16.00 | 13.90-14.20 | yes |
| hadw11-12.qcir | - | - | - | - | - | unfinished |
| ltl2dba_beta6.tlsf.qcir | 16.19 | 14.29 | 0.883 | 15.40-17.04 | 13.86-14.81 | yes |
| **geometric mean** (n=5 identical searches) |  |  | **0.784** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir, chess_solving_mate_in_3_2003_UKR-CH_04.qcir, chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir, chess_solving_mate_in_3_1991_WCSC-15_05.qcir, hadw11-12.qcir

