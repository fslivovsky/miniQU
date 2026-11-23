# Load measurement M1-r2-load-watches-mode1

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -mode=1`
- B (new-r2): `/home/ec2-user/miniqu-work/r2t2/miniQU-final`, sha256 1b6759f85303591cf63eeefd0aceef65ab3f067da24a9ccf004e058a78aee379, args `--seed=1 -mode=1`
- cores 0-47, 4 copies of 12 instances, 3 rounds
- order of the arms: A (2026-11-23T06:37:17), B (2026-11-23T06:42:18), A (2026-11-23T06:47:19), B (2026-11-23T06:52:19), A (2026-11-23T06:57:20), B (2026-11-23T07:02:21)

User CPU seconds, median over all copies and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| DW-sat-08-22-1.qcir | 1.66 | 1.44 | 0.868 | 1.53-2.15 | 1.39-1.54 | yes |
| DW-unsat-09-22-1.qcir | 9.19 | 7.12 | 0.775 | 7.22-12.26 | 6.65-7.63 | yes |
| jctc10-fail.qcir | - | - | - | - | - | unfinished |
| DW-sat-09-26-1.qcir | 6.79 | 4.40 | 0.649 | 4.61-8.30 | 3.92-4.87 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 28.26 | 27.10 | 0.959 | 26.63-29.15 | 26.59-27.50 | different search |
| 9.2.qcir | 16.23 | 12.95 | 0.798 | 15.36-16.61 | 12.61-13.38 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.46 | 2.74 | 1.114 | 2.19-2.76 | 2.58-2.98 | yes |
| chess_solving_mate_in_3_1991_WCSC-15_05.qcir | 11.39 | 11.61 | 1.019 | 9.95-12.76 | 11.15-11.83 | different search |
| 4.1.qcir | 7.01 | 5.94 | 0.847 | 6.87-7.26 | 5.69-6.27 | yes |
| 5.2-1.qcir | 20.45 | 19.26 | 0.942 | 19.51-21.37 | 18.50-19.77 | yes |
| hadw11-12.qcir | 8.93 | 8.20 | 0.919 | 8.44-9.65 | 7.98-8.48 | yes |
| ltl2dba_beta6.tlsf.qcir | 11.12 | 10.64 | 0.957 | 10.54-12.24 | 10.48-10.83 | yes |
| **geometric mean** (n=9 identical searches) |  |  | **0.865** |  |  |  |

Unfinished (timeout or unexpected exit code, excluded): jctc10-fail.qcir

