# Load measurement M1-r2-load-after-mode1

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -mode=1`
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final5`, sha256 dfbd0f64976b470e04e8a674e9731536b944d4087bbf27019af3987d1add8900, args `--seed=1 -mode=1`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T10:09:53), B (2026-11-23T10:14:53), A (2026-11-23T10:19:54), B (2026-11-23T10:24:55), A (2026-11-23T10:29:55), B (2026-11-23T10:34:56)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.77 | 1.37 | 0.775 | 1.55-2.25 | 1.28-1.45 | yes |
| DW-unsat-09-22-1.qcir | 8.91 | 6.76 | 0.759 | 7.50-10.78 | 6.34-7.13 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 6.73 | 4.26 | 0.634 | 5.39-8.42 | 3.67-4.65 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 27.83 | 25.88 | 0.930 | 26.88-28.89 | 25.55-26.47 | different search |
| 9.2.qcir | 16.17 | 12.00 | 0.742 | 15.48-16.90 | 11.67-12.19 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.48 | 2.68 | 1.082 | 2.19-2.77 | 2.56-2.81 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.22 | 11.02 | 0.982 | 10.03-12.06 | 10.75-11.55 | different search |
| 4.1.qcir | 6.99 | 5.58 | 0.798 | 6.85-7.47 | 5.36-5.75 | yes |
| 5.2-1.qcir | 20.43 | 17.98 | 0.880 | 19.60-21.39 | 17.45-18.38 | yes |
| hadw11-12.qcir | 9.01 | 7.64 | 0.847 | 8.70-9.38 | 7.52-7.79 | yes |
| ltl2dba_beta6.tlsf.qcir | 11.13 | 10.24 | 0.920 | 10.67-12.78 | 9.66-10.36 | yes |
| **geometric mean** (n=9 identical searches) |  |  | **0.818** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir

