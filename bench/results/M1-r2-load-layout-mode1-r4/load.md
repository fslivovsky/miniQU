# Load measurement M1-r2-load-layout-mode1-r4

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -mode=1`
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-new`, sha256 59aa524cbd5b4853ec370ef5a5207e5005e23c0d42497fc3281ffbc2f7da94d4, args `--seed=1 -mode=1`
- cores 0-47, 4 copies of 12 instances, 4 rounds
- order of the arms: A (2026-11-23T05:01:49), B (2026-11-23T05:06:49), A (2026-11-23T05:11:50), B (2026-11-23T05:16:51), A (2026-11-23T05:21:51), B (2026-11-23T05:26:52), A (2026-11-23T05:31:53), B (2026-11-23T05:36:53)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.66 | 2.09 | 1.259 | 1.56-2.38 | 1.47-2.71 | yes |
| DW-unsat-09-22-1.qcir | 9.33 | 10.95 | 1.173 | 7.47-11.55 | 8.16-11.89 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 7.14 | 7.11 | 0.995 | 4.56-8.30 | 6.31-7.76 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 27.50 | 27.60 | 1.004 | 26.73-29.06 | 26.38-28.41 | different search |
| 9.2.qcir | 16.38 | 15.44 | 0.942 | 15.57-16.99 | 14.74-16.90 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.49 | 2.57 | 1.028 | 2.23-2.80 | 2.30-2.99 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.28 | 11.47 | 1.017 | 10.13-12.76 | 10.03-13.35 | different search |
| 4.1.qcir | 7.01 | 6.55 | 0.935 | 6.74-7.40 | 6.34-6.87 | yes |
| 5.2-1.qcir | 20.44 | 19.71 | 0.964 | 19.58-21.24 | 18.88-20.73 | yes |
| hadw11-12.qcir | 8.93 | 8.28 | 0.927 | 8.47-9.48 | 7.82-9.20 | yes |
| ltl2dba_beta6.tlsf.qcir | 11.25 | 10.26 | 0.912 | 10.43-12.96 | 9.92-11.93 | yes |
| **geometric mean** (n=9 identical searches) |  |  | **1.009** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir

