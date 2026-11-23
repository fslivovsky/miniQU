# Load measurement M1-r2-load-layout-mode1

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -mode=1`
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-new`, sha256 59aa524cbd5b4853ec370ef5a5207e5005e23c0d42497fc3281ffbc2f7da94d4, args `--seed=1 -mode=1`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T04:27:09), B (2026-11-23T04:32:09), A (2026-11-23T04:37:10), B (2026-11-23T04:42:10), A (2026-11-23T04:47:11), B (2026-11-23T04:52:12)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.64 | 2.00 | 1.221 | 1.55-1.89 | 1.48-2.83 | yes |
| DW-unsat-09-22-1.qcir | 8.89 | 10.34 | 1.163 | 7.84-10.65 | 7.99-12.44 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 7.07 | 7.19 | 1.016 | 5.35-8.43 | 6.42-7.92 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 27.36 | 27.76 | 1.014 | 26.52-28.33 | 26.53-28.38 | different search |
| 9.2.qcir | 16.16 | 15.44 | 0.955 | 15.64-16.79 | 14.71-15.95 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.49 | 2.60 | 1.047 | 2.28-3.03 | 2.27-2.98 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.19 | 11.51 | 1.029 | 9.81-12.82 | 10.04-12.20 | different search |
| 4.1.qcir | 7.06 | 6.50 | 0.921 | 6.93-7.43 | 6.33-6.70 | yes |
| 5.2-1.qcir | 20.26 | 19.66 | 0.970 | 19.65-21.40 | 19.01-20.42 | yes |
| hadw11-12.qcir | 8.95 | 8.22 | 0.919 | 8.53-9.54 | 7.73-8.83 | yes |
| ltl2dba_beta6.tlsf.qcir | 11.10 | 10.51 | 0.947 | 10.66-11.85 | 9.85-12.59 | yes |
| **geometric mean** (n=9 identical searches) |  |  | **1.013** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir

