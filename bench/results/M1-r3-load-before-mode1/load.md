# Load measurement M1-r3-load-before-mode1

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -mode=1`
- B (r2): `/home/ec2-user/miniqu-work/build/bench-M1-r2/miniQU`, sha256 30bd8fe6b956764096067c8096b6c588e5fc3d0740a62bc352d15851c5eee968, args `--seed=1 -mode=1`
- placement: L3 groups, cores kept busy (every core loops over its instance until every core has completed a run; timeout 60 s per run); 2 rounds
- group 0 on cores 0,1,2,3,4,5,6,7: 8 instances
- group 1 on cores 8,9,10,11,12,13,14,15: 8 instances
- group 2 on cores 16,17,18,19,20,21,22,23: 8 instances
- group 3 on cores 24,25,26,27,28,29,30,31: 8 instances
- group 4 on cores 32,33,34,35,36,37,38,39: 8 instances
- group 5 on cores 40,41,42,43,44,45,46,47: 8 instances
- order of the arms: A (2026-11-23T16:08:43), B (2026-11-23T16:09:45), A (2026-11-23T16:10:46), B (2026-11-23T16:11:48)

User CPU seconds, median over all completed runs and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| CM-unsat-07-01-06-2.qcir | - | - | - | - | - | unfinished |
| DW-sat-08-22-1.qcir | 1.64 | 2.60 | 1.590 | 1.53-2.52 | 2.44-2.79 | yes |
| DW-sat-08-23-1.qcir | 1.53 | 2.69 | 1.759 | 1.38-2.66 | 2.60-2.81 | yes |
| DW-sat-09-26-1.qcir | 8.05 | 8.28 | 1.029 | 7.34-8.44 | 8.06-8.52 | yes |
| DW-unsat-09-22-1.qcir | 14.58 | 19.22 | 1.319 | 10.15-16.89 | 18.93-19.57 | yes |
| DW-unsat-09-23-1.qcir | 18.64 | 20.17 | 1.082 | 16.89-19.27 | 19.70-20.28 | yes |
| DW-unsat-10-25-1.qcir | - | - | - | - | - | unfinished |
| DW-unsat-11-26-1.qcir | - | - | - | - | - | unfinished |
| 10.1.qcir | 2.01 | 1.80 | 0.895 | 1.90-2.12 | 1.72-1.87 | yes |
| 10.2.qcir | 1.48 | 1.13 | 0.764 | 1.33-1.62 | 1.06-1.27 | yes |
| 11.1.qcir | 33.18 | 35.14 | 1.059 | 33.06-33.29 | 35.09-35.19 | yes |
| 2.1.qcir | - | - | - | - | - | unfinished |
| 2.2.qcir | - | - | - | - | - | unfinished |
| 3.1.qcir | 43.51 | 47.50 | 1.092 | 43.44-43.58 | 46.36-48.65 | yes |
| 3.2.qcir | 1.02 | 0.76 | 0.744 | 0.93-1.14 | 0.69-0.82 | yes |
| 4.1.qcir | 7.11 | 7.94 | 1.116 | 6.81-7.47 | 7.73-8.25 | yes |
| 5.2-1.qcir | 28.20 | 35.54 | 1.260 | 28.05-28.50 | 35.14-35.94 | yes |
| 5.2-2.qcir | - | - | - | - | - | unfinished |
| 5.2-3.qcir | - | - | - | - | - | unfinished |
| 8.1.qcir | 3.96 | 4.09 | 1.033 | 3.81-4.11 | 3.96-4.21 | yes |
| 9.1.qcir | 1.97 | 1.51 | 0.764 | 1.84-2.07 | 1.44-1.59 | yes |
| 9.2.qcir | 18.98 | 18.85 | 0.993 | 18.93-19.44 | 18.63-19.24 | yes |
| 9.3.qcir | 2.39 | 2.39 | 0.999 | 2.30-2.50 | 2.30-2.44 | yes |
| CM-sat-04-01-06-3.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 1.36 | 1.51 | 1.107 | 1.25-1.70 | 1.46-1.87 | yes |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | 0.58 | 0.62 | 1.065 | 0.51-0.69 | 0.58-0.65 | yes |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 0.72 | 0.78 | 1.084 | 0.66-0.91 | 0.74-0.96 | yes |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 0.76 | 0.84 | 1.096 | 0.70-0.97 | 0.80-0.92 | yes |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 0.54 | 0.53 | 0.987 | 0.47-0.67 | 0.48-0.66 | yes |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 0.71 | 0.78 | 1.103 | 0.65-0.89 | 0.73-0.83 | yes |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | 0.27 | 0.25 | 0.932 | 0.21-0.32 | 0.21-0.28 | yes |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | 0.64 | 0.69 | 1.082 | 0.59-0.78 | 0.64-0.76 | yes |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 15.82 | 17.21 | 1.088 | 14.58-16.57 | 16.79-17.53 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 40.80 | 48.23 | 1.182 | 39.30-42.30 | 48.08-48.38 | different search |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 5.16 | 5.76 | 1.116 | 4.46-5.54 | 5.65-5.86 | different search |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 2.94 | 3.15 | 1.070 | 2.65-3.35 | 3.07-3.20 | yes |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 16.97 | 20.06 | 1.182 | 16.39-17.28 | 19.86-20.48 | yes |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 2.41 | 2.64 | 1.095 | 2.16-2.91 | 2.57-2.69 | yes |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 8.32 | 9.40 | 1.130 | 7.76-9.66 | 9.12-9.49 | yes |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 18.16 | 19.22 | 1.058 | 16.25-19.98 | 18.76-19.48 | yes |
| ex92_7S700.qcir | - | - | - | - | - | unfinished |
| finan01-finan01_mov.qcir | - | - | - | - | - | unfinished |
| finan01_mov-finan01.qcir | - | - | - | - | - | unfinished |
| finding_nemo_1.tlsf.qcir | 10.95 | 10.89 | 0.994 | 10.67-11.78 | 10.76-11.30 | different search |
| genbuf10b4n.unsat.qcir | - | - | - | - | - | unfinished |
| genbuf9b4n.unsat.qcir | - | - | - | - | - | unfinished |
| hadw10-11.qcir | 1.69 | 1.87 | 1.102 | 1.58-1.88 | 1.77-2.01 | yes |
| hadw11-12.qcir | 7.73 | 7.61 | 0.985 | 7.56-8.02 | 7.32-8.05 | yes |
| **geometric mean** (n=32 identical searches) |  |  | **1.067** |  |  |  |

Per group (geometric mean of B / A over the identical searches of the group):

| group | first instance | chosen as | n | geometric mean B / A |
|---|---:|---:|---:|---:|
| 0 | CM-unsat-07-01-06-2.qcir | CM/DW (mandatory). Reviewer's L3 reproducer of round 2: DW-sat/unsat 08-22 ... 11-26 run 1.14-1.27 times slower in benchmark runs; 6 instances with identical searches at 2-52 s. | 5 | 1.326 |
| 1 | 10.1.qcir | numeric, the 4.1 region (10.1 ... 4.1): 6 instances with identical searches at 1.1-43 s, long numeric runs next to short ones. | 6 | 0.932 |
| 2 | 5.2-1.qcir | numeric, the 5.2-1 region (5.2-1 ... CM-sat-04-01-06-3): 4 instances with identical searches (8.1, 9.1, 9.2, 9.3) at 2-17 s. No third family has a window with three qualifying instances, so this is a second numeric window. | 5 | 0.997 |
| 3 | chess_solving_mate_in_2_1982_WCSC-6_02.qcir | chess mate_in_2 (1982 ... 2002): 3 instances with identical searches at 1.2-1.4 s, short runs that change often. | 8 | 1.055 |
| 4 | chess_solving_mate_in_3_2001_UKR-CH_06.qcir | chess mate_in_3 (2001_UKR-CH_06 ... 2014_FRA-CH_03): 6 instances with identical searches at 5-13 s, contains chess_solving_mate_in_3_2014_FRA-CH_03. | 6 | 1.103 |
| 5 | ex92_7S700.qcir | hadw10-11, hadw11-12 with ex, finan, finding_nemo and genbuf neighbours: 3 instances with identical searches (finding_nemo_1, hadw10-11, hadw11-12) at 3-12 s. | 2 | 1.042 |

Unfinished (timeout or unexpected exit code, excluded): CM-unsat-07-01-06-2.qcir, DW-unsat-10-25-1.qcir, DW-unsat-11-26-1.qcir, 2.1.qcir, 2.2.qcir, 5.2-2.qcir, 5.2-3.qcir, CM-sat-04-01-06-3.qcir, ex92_7S700.qcir, finan01-finan01_mov.qcir, finan01_mov-finan01.qcir, genbuf10b4n.unsat.qcir, genbuf9b4n.unsat.qcir

