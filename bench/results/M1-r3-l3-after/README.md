# M1-R3-T3 measurements (WatchList, 32-byte record)

Binaries: base = /home/ec2-user/miniqu-work/baseline/miniQU, r2 = build/bench-M1-r2/miniQU
(sha256 30bd8fe6), new = build/bench-M1-r3-pre/miniQU (commit b2018c1, Release). Lower half (0-47),
machine otherwise idle, 96 cores.

- `default.md`, `mode1.md`, `dl.md` (+ `.raw.txt`): `bench/l3.sh OUT base= r2= new=`, without extra
  arguments, `-a -mode=1`, `-a -dl`; 2 rounds, 40 s.
- `cross-nb.txt`: `bench/cross.sh DW-sat-08-23-1` with NEW = new and NEW = r2;
  `bench/nb.sh DW-unsat-11-26-1 12 DW-sat-08-23-1` with neighbours base, r2, new.

Same search (`/home/ec2-user/miniqu-work/r2t2/f1.py r2 new OUT main`: load instances seeds 1 and 0,
smoke set, corpus search seeds 151-300; six configurations; 60 s): compared 1513, identical 1513,
different 0, skipped (timeout of either arm) 161. Ticks and proof bytes (`-proof=FILE`, `cmp`), r2 vs new:

| instance | config | ticks | proof |
|---|---|---:|---|
| 3.2 | default | 9949014 | identical (37102729 bytes) |
| 3.2 | -mode=1 | 9949004 | identical (37102736 bytes) |
| 5-5-6-10-3-7-EdAd | default | 530003 | identical (253276 bytes) |
| 5-5-6-10-3-7-EdAd | -mode=1 | 4342937 | identical (1072078 bytes) |
| 9.1 | default | 21989501 | identical (67045720 bytes) |
| 9.1 | -mode=1 | 118373199 | identical (68283715 bytes) |
| DW-sat-08-22-1 | default | 68962424 | identical (17839756 bytes) |
| DW-sat-08-22-1 | -mode=1 | 29021864 | identical (12858038 bytes) |
| bt-2x4_13.ig | default | 16416418 | identical (9123953 bytes) |
| bt-2x4_13.ig | -mode=1 | 72634900 | identical (37252446 bytes) |

Ticks equal between r2 and new in all ten runs.

Peak RSS (`/usr/bin/time -v`, one process, default options, KB):

| instance | r2 | new | new / r2 |
|---|---:|---:|---:|
| 1.3 | 1390432 | 1133920 | 0.816 |
| 5.2-1 | 383756 | 317784 | 0.828 |
| DW-sat-08-22-1 | 33140 | 28524 | 0.861 |
| amba2f9n.sat | 21904, 21904, 21912 | 22388, 22460, 22396 | 1.022 |

amba2f9n.sat (1569 variables, 1.59 M conflicts, identical search, 65 s): the excess (about 0.5 MB)
is the allocator, not the layout: the same code with `malloc` + `memcpy` + `free` instead of
`realloc` in `WatchList::grow` (experiment, not committed) peaks at 21732 KB there and at 1134356,
317712, 28516 KB on the other three.
