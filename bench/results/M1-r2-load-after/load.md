# Load measurement M1-r2-load-after

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 `
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final5`, sha256 dfbd0f64976b470e04e8a674e9731536b944d4087bbf27019af3987d1add8900, args `--seed=1 `
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T09:36:42), B (2026-11-23T09:37:15), A (2026-11-23T09:37:45), B (2026-11-23T09:38:18), A (2026-11-23T09:38:47), B (2026-11-23T09:39:19)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.96 | 1.58 | 0.808 | 1.88-3.75 | 1.50-1.65 | yes |
| DW-unsat-09-22-1.qcir | 9.92 | 6.69 | 0.675 | 8.75-10.64 | 6.35-6.95 | yes |
| jctc10-fail.qcir | 7.33 | 6.44 | 0.879 | 5.90-8.24 | 4.85-7.10 | yes |
| DW-sat-09-26-1.qcir | 3.79 | 2.22 | 0.586 | 3.38-4.10 | 1.97-2.39 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.62 | 9.31 | 0.968 | 8.70-11.24 | 8.93-10.01 | yes |
| 9.2.qcir | 13.85 | 10.49 | 0.757 | 12.68-15.27 | 10.08-11.39 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 12.31 | 11.47 | 0.932 | 11.38-14.72 | 10.86-12.11 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 8.19 | 7.78 | 0.949 | 7.38-9.13 | 7.59-8.16 | yes |
| 4.1.qcir | 8.23 | 6.61 | 0.803 | 7.99-8.52 | 6.39-6.71 | yes |
| 5.2-1.qcir | 31.75 | 28.10 | 0.885 | 30.79-32.59 | 27.30-29.04 | yes |
| hadw11-12.qcir | 6.29 | 5.63 | 0.895 | 6.00-6.65 | 5.49-5.83 | yes |
| ltl2dba_beta6.tlsf.qcir | 12.28 | 10.83 | 0.881 | 11.55-13.58 | 10.15-11.42 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **0.827** |  |  |  |

