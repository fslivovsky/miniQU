# Load measurement M1-r3-load-before

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1`
- B (r2): `/home/ec2-user/miniqu-work/build/bench-M1-r2/miniQU`, sha256 30bd8fe6b956764096067c8096b6c588e5fc3d0740a62bc352d15851c5eee968, args `--seed=1`
- placement: L3 groups, cores kept busy (every core loops over its instance until every core has completed a run; timeout 60 s per run); 2 rounds
- group 0 on cores 0,1,2,3,4,5,6,7: 8 instances
- group 1 on cores 8,9,10,11,12,13,14,15: 8 instances
- group 2 on cores 16,17,18,19,20,21,22,23: 8 instances
- group 3 on cores 24,25,26,27,28,29,30,31: 8 instances
- group 4 on cores 32,33,34,35,36,37,38,39: 8 instances
- group 5 on cores 40,41,42,43,44,45,46,47: 8 instances
- order of the arms: A (2026-11-23T16:04:36), B (2026-11-23T16:05:38), A (2026-11-23T16:06:39), B (2026-11-23T16:07:41)

User CPU seconds, median over all completed runs and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| CM-unsat-07-01-06-2.qcir | - | - | - | - | - | unfinished |
| DW-sat-08-22-1.qcir | 2.00 | 3.19 | 1.594 | 1.88-3.21 | 2.96-3.50 | yes |
| DW-sat-08-23-1.qcir | 1.52 | 2.70 | 1.771 | 1.44-2.77 | 2.57-2.86 | yes |
| DW-sat-09-26-1.qcir | 3.75 | 3.77 | 1.004 | 3.26-4.00 | 3.68-3.93 | yes |
| DW-unsat-09-22-1.qcir | 17.77 | 19.04 | 1.072 | 15.21-18.47 | 18.55-19.54 | yes |
| DW-unsat-09-23-1.qcir | 27.77 | 32.11 | 1.156 | 27.29-30.43 | 31.75-32.46 | yes |
| DW-unsat-10-25-1.qcir | 50.97 | 53.65 | 1.053 | 49.50-52.44 | 53.61-53.69 | yes |
| DW-unsat-11-26-1.qcir | - | - | - | - | - | unfinished |
| 10.1.qcir | 2.01 | 1.76 | 0.875 | 1.91-2.11 | 1.67-1.86 | yes |
| 10.2.qcir | 1.46 | 1.13 | 0.773 | 1.37-1.57 | 1.04-1.18 | yes |
| 11.1.qcir | 28.42 | 28.80 | 1.013 | 28.13-28.61 | 28.67-28.87 | yes |
| 2.1.qcir | - | - | - | - | - | unfinished |
| 2.2.qcir | - | - | - | - | - | unfinished |
| 3.1.qcir | 43.31 | 45.82 | 1.058 | 42.91-43.71 | 45.61-46.02 | yes |
| 3.2.qcir | 1.01 | 0.74 | 0.739 | 0.92-1.09 | 0.68-0.83 | yes |
| 4.1.qcir | 8.40 | 8.85 | 1.053 | 8.16-8.82 | 8.57-9.24 | yes |
| 5.2-1.qcir | - | - | - | - | - | unfinished |
| 5.2-2.qcir | - | - | - | - | - | unfinished |
| 5.2-3.qcir | - | - | - | - | - | unfinished |
| 8.1.qcir | 3.74 | 3.83 | 1.024 | 3.57-3.85 | 3.71-3.98 | yes |
| 9.1.qcir | 2.18 | 1.72 | 0.789 | 2.09-2.32 | 1.65-1.82 | yes |
| 9.2.qcir | 17.05 | 16.29 | 0.955 | 16.83-17.34 | 16.07-16.79 | yes |
| 9.3.qcir | 2.40 | 2.30 | 0.960 | 2.26-2.52 | 2.24-2.37 | yes |
| CM-sat-04-01-06-3.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 1.40 | 1.45 | 1.032 | 1.25-1.72 | 1.40-1.49 | yes |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | 0.56 | 0.57 | 1.006 | 0.46-0.65 | 0.53-0.67 | yes |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 0.63 | 0.64 | 1.020 | 0.56-0.77 | 0.60-0.73 | yes |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 1.54 | 1.68 | 1.087 | 1.45-1.95 | 1.62-1.72 | yes |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 0.61 | 0.60 | 0.993 | 0.53-0.74 | 0.57-0.66 | yes |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 1.28 | 1.37 | 1.069 | 1.17-1.62 | 1.32-1.40 | yes |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | 0.25 | 0.23 | 0.904 | 0.21-0.30 | 0.19-0.28 | yes |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | 0.57 | 0.59 | 1.035 | 0.52-0.69 | 0.55-0.72 | yes |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | 6.99 | 7.83 | 1.120 | 6.66-8.37 | 7.68-7.99 | yes |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | 9.88 | 10.98 | 1.111 | 9.22-10.84 | 10.79-14.49 | yes |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | 4.25 | 5.25 | 1.235 | 3.85-4.54 | 5.16-5.38 | different search |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | 4.66 | 5.04 | 1.083 | 4.25-5.41 | 4.86-5.16 | yes |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | 11.49 | 17.84 | 1.553 | 10.49-12.75 | 17.44-18.20 | different search |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | 13.81 | 14.50 | 1.050 | 12.20-16.22 | 14.13-14.85 | yes |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | 6.56 | 6.79 | 1.035 | 5.73-7.47 | 6.64-6.95 | yes |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | 15.45 | 15.75 | 1.019 | 14.57-16.50 | 15.60-16.09 | yes |
| ex92_7S700.qcir | - | - | - | - | - | unfinished |
| finan01-finan01_mov.qcir | - | - | - | - | - | unfinished |
| finan01_mov-finan01.qcir | - | - | - | - | - | unfinished |
| finding_nemo_1.tlsf.qcir | 14.32 | 14.57 | 1.018 | 13.72-15.97 | 13.86-14.76 | yes |
| genbuf10b4n.unsat.qcir | - | - | - | - | - | unfinished |
| genbuf9b4n.unsat.qcir | - | - | - | - | - | unfinished |
| hadw10-11.qcir | 3.43 | 3.50 | 1.019 | 3.28-3.76 | 3.33-3.70 | yes |
| hadw11-12.qcir | 5.36 | 5.54 | 1.035 | 5.10-5.59 | 5.33-5.79 | yes |
| **geometric mean** (n=33 identical searches) |  |  | **1.032** |  |  |  |

Per group (geometric mean of B / A over the identical searches of the group):

| group | first instance | chosen as | n | geometric mean B / A |
|---|---:|---:|---:|---:|
| 0 | CM-unsat-07-01-06-2.qcir | CM/DW (mandatory). Reviewer's L3 reproducer of round 2: DW-sat/unsat 08-22 ... 11-26 run 1.14-1.27 times slower in benchmark runs; 6 instances with identical searches at 2-52 s. | 6 | 1.243 |
| 1 | 10.1.qcir | numeric, the 4.1 region (10.1 ... 4.1): 6 instances with identical searches at 1.1-43 s, long numeric runs next to short ones. | 6 | 0.909 |
| 2 | 5.2-1.qcir | numeric, the 5.2-1 region (5.2-1 ... CM-sat-04-01-06-3): 4 instances with identical searches (8.1, 9.1, 9.2, 9.3) at 2-17 s. No third family has a window with three qualifying instances, so this is a second numeric window. | 4 | 0.928 |
| 3 | chess_solving_mate_in_2_1982_WCSC-6_02.qcir | chess mate_in_2 (1982 ... 2002): 3 instances with identical searches at 1.2-1.4 s, short runs that change often. | 8 | 1.017 |
| 4 | chess_solving_mate_in_3_2001_UKR-CH_06.qcir | chess mate_in_3 (2001_UKR-CH_06 ... 2014_FRA-CH_03): 6 instances with identical searches at 5-13 s, contains chess_solving_mate_in_3_2014_FRA-CH_03. | 6 | 1.069 |
| 5 | ex92_7S700.qcir | hadw10-11, hadw11-12 with ex, finan, finding_nemo and genbuf neighbours: 3 instances with identical searches (finding_nemo_1, hadw10-11, hadw11-12) at 3-12 s. | 3 | 1.024 |

Unfinished (timeout or unexpected exit code, excluded): CM-unsat-07-01-06-2.qcir, DW-unsat-11-26-1.qcir, 2.1.qcir, 2.2.qcir, 5.2-1.qcir, 5.2-2.qcir, 5.2-3.qcir, CM-sat-04-01-06-3.qcir, ex92_7S700.qcir, finan01-finan01_mov.qcir, finan01_mov-finan01.qcir, genbuf10b4n.unsat.qcir, genbuf9b4n.unsat.qcir

