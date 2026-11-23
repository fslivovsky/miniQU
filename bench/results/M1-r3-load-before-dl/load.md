# Load measurement M1-r3-load-before-dl

- A (baseline): `/home/ec2-user/miniqu-work/baseline/miniQU`, sha256 10ff614c6694e5f8170c1cc65a616660236ef7158ae08af4e7ccf43b8b71c25b, args `-rnd-init -rnd-seed=1 -dl`
- B (r2): `/home/ec2-user/miniqu-work/build/bench-M1-r2/miniQU`, sha256 30bd8fe6b956764096067c8096b6c588e5fc3d0740a62bc352d15851c5eee968, args `--seed=1 -dl`
- placement: L3 groups, cores kept busy (every core loops over its instance until every core has completed a run; timeout 60 s per run); 2 rounds
- group 0 on cores 0,1,2,3,4,5,6,7: 8 instances
- group 1 on cores 8,9,10,11,12,13,14,15: 8 instances
- group 2 on cores 16,17,18,19,20,21,22,23: 8 instances
- group 3 on cores 24,25,26,27,28,29,30,31: 8 instances
- group 4 on cores 32,33,34,35,36,37,38,39: 8 instances
- group 5 on cores 40,41,42,43,44,45,46,47: 8 instances
- order of the arms: A (2026-11-23T17:17:35), B (2026-11-23T17:18:37), A (2026-11-23T17:19:39), B (2026-11-23T17:20:41)

User CPU seconds, median over all completed runs and rounds; ratio is B / A.

| instance | A median | B median | B / A | A min-max | B min-max | identical search |
|---|---:|---:|---:|---:|---:|---:|
| CM-unsat-07-01-06-2.qcir | - | - | - | - | - | unfinished |
| DW-sat-08-22-1.qcir | 11.86 | 13.15 | 1.109 | 9.12-13.41 | 12.10-14.39 | yes |
| DW-sat-08-23-1.qcir | 4.97 | 6.50 | 1.309 | 3.82-6.32 | 6.03-6.88 | different search |
| DW-sat-09-26-1.qcir | 41.75 | 37.89 | 0.908 | 41.70-41.81 | 37.52-38.26 | different search |
| DW-unsat-09-22-1.qcir | 7.84 | 4.20 | 0.536 | 5.90-8.71 | 4.10-4.35 | different search |
| DW-unsat-09-23-1.qcir | 2.69 | 2.49 | 0.928 | 2.43-3.04 | 2.42-2.59 | different search |
| DW-unsat-10-25-1.qcir | 14.43 | 17.95 | 1.243 | 12.94-15.15 | 17.76-18.11 | different search |
| DW-unsat-11-26-1.qcir | - | - | - | - | - | unfinished |
| 10.1.qcir | 3.71 | 3.53 | 0.951 | 3.62-3.82 | 3.36-3.59 | yes |
| 10.2.qcir | 1.89 | 1.58 | 0.833 | 1.79-1.98 | 1.44-1.66 | yes |
| 11.1.qcir | 30.56 | 29.95 | 0.980 | 30.43-30.69 | 29.44-30.30 | yes |
| 2.1.qcir | - | - | - | - | - | unfinished |
| 2.2.qcir | - | - | - | - | - | unfinished |
| 3.1.qcir | - | - | - | - | - | unfinished |
| 3.2.qcir | 1.42 | 1.17 | 0.824 | 1.34-1.52 | 1.07-1.33 | yes |
| 4.1.qcir | 6.65 | 6.65 | 1.000 | 6.38-6.73 | 6.39-7.24 | yes |
| 5.2-1.qcir | 17.07 | 20.12 | 1.179 | 16.73-17.28 | 19.52-20.25 | yes |
| 5.2-2.qcir | - | - | - | - | - | unfinished |
| 5.2-3.qcir | - | - | - | - | - | unfinished |
| 8.1.qcir | 4.34 | 4.33 | 0.998 | 4.22-4.62 | 4.18-4.52 | yes |
| 9.1.qcir | 2.30 | 1.82 | 0.793 | 2.22-2.41 | 1.75-1.92 | yes |
| 9.2.qcir | 19.59 | 17.79 | 0.908 | 19.32-19.81 | 17.47-18.03 | yes |
| 9.3.qcir | 3.25 | 3.00 | 0.922 | 3.14-3.39 | 2.92-3.34 | yes |
| CM-sat-04-01-06-3.qcir | 30.54 | 44.90 | 1.470 | 30.43-31.51 | 44.75-45.06 | different search |
| chess_solving_mate_in_2_1982_WCSC-6_02.qcir | 18.80 | 18.15 | 0.965 | 17.99-19.30 | 17.60-18.52 | yes |
| chess_solving_mate_in_2_1983_FIN-CH-4_01.qcir | 4.14 | 4.13 | 0.996 | 3.54-4.57 | 4.07-4.26 | yes |
| chess_solving_mate_in_2_1987_FIN-CH-8_01.qcir | 6.85 | 6.85 | 1.001 | 5.66-7.59 | 6.61-7.08 | yes |
| chess_solving_mate_in_2_1991_GER-CH-15_01.qcir | 2.41 | 2.50 | 1.038 | 1.85-2.83 | 2.40-2.60 | yes |
| chess_solving_mate_in_2_1996_FIN-CH-17_03.qcir | 8.33 | 8.35 | 1.002 | 7.83-8.79 | 8.04-8.65 | different search |
| chess_solving_mate_in_2_1997_WCCC-OPEN-40_03.qcir | 23.68 | 19.60 | 0.828 | 22.30-24.95 | 19.38-20.45 | different search |
| chess_solving_mate_in_2_1998_GBR-CH-19_01.qcir | 5.97 | 6.08 | 1.019 | 5.32-6.75 | 5.87-6.32 | yes |
| chess_solving_mate_in_2_2002_MAC-CH-6_03.qcir | 5.25 | 5.35 | 1.019 | 4.67-5.74 | 5.13-6.26 | yes |
| chess_solving_mate_in_3_2001_UKR-CH_06.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2003_UKR-CH_04.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2008_ISC-4B_07.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2010_UKR-CH_04.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir | - | - | - | - | - | unfinished |
| chess_solving_mate_in_3_2014_FRA-CH_03.qcir | - | - | - | - | - | unfinished |
| ex92_7S700.qcir | - | - | - | - | - | unfinished |
| finan01-finan01_mov.qcir | - | - | - | - | - | unfinished |
| finan01_mov-finan01.qcir | - | - | - | - | - | unfinished |
| finding_nemo_1.tlsf.qcir | 7.13 | 6.96 | 0.976 | 6.55-7.87 | 6.75-7.11 | yes |
| genbuf10b4n.unsat.qcir | - | - | - | - | - | unfinished |
| genbuf9b4n.unsat.qcir | - | - | - | - | - | unfinished |
| hadw10-11.qcir | 40.70 | 38.91 | 0.956 | 40.03-41.37 | 38.84-38.97 | yes |
| hadw11-12.qcir | - | - | - | - | - | unfinished |
| **geometric mean** (n=19 identical searches) |  |  | **0.968** |  |  |  |

Per group (geometric mean of B / A over the identical searches of the group):

| group | first instance | chosen as | n | geometric mean B / A |
|---|---:|---:|---:|---:|
| 0 | CM-unsat-07-01-06-2.qcir | CM/DW (mandatory). Reviewer's L3 reproducer of round 2: DW-sat/unsat 08-22 ... 11-26 run 1.14-1.27 times slower in benchmark runs; 6 instances with identical searches at 2-52 s. | 1 | 1.109 |
| 1 | 10.1.qcir | numeric, the 4.1 region (10.1 ... 4.1): 6 instances with identical searches at 1.1-43 s, long numeric runs next to short ones. | 5 | 0.915 |
| 2 | 5.2-1.qcir | numeric, the 5.2-1 region (5.2-1 ... CM-sat-04-01-06-3): 4 instances with identical searches (8.1, 9.1, 9.2, 9.3) at 2-17 s. No third family has a window with three qualifying instances, so this is a second numeric window. | 5 | 0.952 |
| 3 | chess_solving_mate_in_2_1982_WCSC-6_02.qcir | chess mate_in_2 (1982 ... 2002): 3 instances with identical searches at 1.2-1.4 s, short runs that change often. | 6 | 1.006 |
| 4 | chess_solving_mate_in_3_2001_UKR-CH_06.qcir | chess mate_in_3 (2001_UKR-CH_06 ... 2014_FRA-CH_03): 6 instances with identical searches at 5-13 s, contains chess_solving_mate_in_3_2014_FRA-CH_03. | 0 | - |
| 5 | ex92_7S700.qcir | hadw10-11, hadw11-12 with ex, finan, finding_nemo and genbuf neighbours: 3 instances with identical searches (finding_nemo_1, hadw10-11, hadw11-12) at 3-12 s. | 2 | 0.966 |

Unfinished (timeout or unexpected exit code, excluded): CM-unsat-07-01-06-2.qcir, DW-unsat-11-26-1.qcir, 2.1.qcir, 2.2.qcir, 3.1.qcir, 5.2-2.qcir, 5.2-3.qcir, chess_solving_mate_in_3_2001_UKR-CH_06.qcir, chess_solving_mate_in_3_2003_UKR-CH_04.qcir, chess_solving_mate_in_3_2008_ISC-4B_07.qcir, chess_solving_mate_in_3_2010_UKR-CH_04.qcir, chess_solving_mate_in_3_2011_UKR-OPEN-25_04.qcir, chess_solving_mate_in_3_2012_GRE-CH-11_02.qcir, chess_solving_mate_in_3_2012_NED-CH-18B_04.qcir, chess_solving_mate_in_3_2014_FRA-CH_03.qcir, ex92_7S700.qcir, finan01-finan01_mov.qcir, finan01_mov-finan01.qcir, genbuf10b4n.unsat.qcir, genbuf9b4n.unsat.qcir, hadw11-12.qcir

