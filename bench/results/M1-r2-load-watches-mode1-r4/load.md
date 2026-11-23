# Load measurement M1-r2-load-watches-mode1-r4

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -mode=1`
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final`, sha256 1b6759f85303591cf63eeefd0aceef65ab3f067da24a9ccf004e058a78aee379, args `--seed=1 -mode=1`
- cores 0-47, 4 copies of 12 instances, 4 rounds
- order of the arms: A (2026-11-23T07:07:32), B (2026-11-23T07:12:33), A (2026-11-23T07:17:34), B (2026-11-23T07:22:34), A (2026-11-23T07:27:35), B (2026-11-23T07:32:35), A (2026-11-23T07:37:36), B (2026-11-23T07:42:37)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.61 | 1.40 | 0.871 | 1.53-1.83 | 1.37-1.53 | yes |
| DW-unsat-09-22-1.qcir | 8.85 | 7.25 | 0.819 | 7.29-11.14 | 6.61-7.78 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 7.25 | 4.51 | 0.622 | 4.54-8.07 | 3.86-5.00 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 27.66 | 27.07 | 0.979 | 26.47-28.78 | 26.64-27.49 | different search |
| 9.2.qcir | 16.33 | 12.87 | 0.788 | 15.60-17.15 | 12.53-13.72 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.45 | 2.75 | 1.120 | 2.27-3.01 | 2.65-2.97 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.30 | 11.57 | 1.024 | 9.65-12.37 | 10.97-11.82 | different search |
| 4.1.qcir | 6.99 | 5.97 | 0.854 | 6.84-7.34 | 5.65-6.21 | yes |
| 5.2-1.qcir | 20.27 | 19.28 | 0.951 | 19.52-21.32 | 18.50-19.85 | yes |
| hadw11-12.qcir | 8.75 | 8.20 | 0.937 | 8.47-9.87 | 7.96-8.43 | yes |
| ltl2dba_beta6.tlsf.qcir | 11.13 | 10.65 | 0.956 | 10.50-11.51 | 9.49-10.80 | yes |
| **geometric mean** (n=9 identical searches) |  |  | **0.870** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir

