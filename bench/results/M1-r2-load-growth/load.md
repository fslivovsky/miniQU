# Load measurement M1-r2-load-growth

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 `
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final3`, sha256 d690db6523e7dd5f19d908dd7777996509bf7d9988e27299469c4f95a28a440d, args `--seed=1 `
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T08:08:15), B (2026-11-23T08:08:49), A (2026-11-23T08:09:18), B (2026-11-23T08:09:51), A (2026-11-23T08:10:20), B (2026-11-23T08:10:53)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 2.22 | 1.56 | 0.704 | 1.87-2.89 | 1.51-1.66 | yes |
| DW-unsat-09-22-1.qcir | 9.80 | 6.73 | 0.687 | 8.59-11.42 | 6.44-6.98 | yes |
| jctc10-fail.qcir | 7.11 | 6.22 | 0.875 | 6.16-8.45 | 4.84-7.01 | yes |
| DW-sat-09-26-1.qcir | 3.79 | 2.23 | 0.590 | 3.58-4.12 | 2.00-2.41 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 10.11 | 9.36 | 0.926 | 8.78-11.62 | 8.90-9.95 | yes |
| 9.2.qcir | 13.94 | 10.58 | 0.759 | 12.73-14.84 | 9.99-11.36 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 12.36 | 11.47 | 0.928 | 11.36-13.88 | 10.82-12.03 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 8.73 | 7.78 | 0.891 | 7.21-9.19 | 7.57-8.07 | yes |
| 4.1.qcir | 8.22 | 6.61 | 0.804 | 8.01-8.55 | 6.49-6.69 | yes |
| 5.2-1.qcir | 31.84 | 28.18 | 0.885 | 30.70-33.00 | 27.29-28.92 | yes |
| hadw11-12.qcir | 6.17 | 5.52 | 0.895 | 5.97-6.42 | 5.45-5.75 | yes |
| ltl2dba_beta6.tlsf.qcir | 12.36 | 10.74 | 0.869 | 11.57-13.56 | 10.26-11.25 | yes |
| **geometric mean** (n=12 identical searches) |  |  | **0.810** |  |  |  |

