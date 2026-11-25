# Hand-over test report (rewrite/cadical-style, head b80f334)

Run 2026-11-25 01:52-02:10 UTC on a 48-core machine (benchmark jobs on cores 24-47, 24 jobs, 8 GB;
everything else on cores 0-23). Nothing was minimised or fixed. No timing claims.

## What ran
1. Release build from scratch in `/home/ec2-user/miniqu-work/build/handover`: no warnings.
2. `ctest`: 45 of 45 tests passed (unit tests, fuzz, encoding-diff, regress-limits, bench tools).
3. `tests/regress.sh -s 1:50 -M all -S -j 24 BUILD/miniQU` (whole matrix, seeds 1:50, no smoke set;
   log `/home/ec2-user/miniqu-work/logs/handover-regress.log`). No wrong verdict, no rejected proof, no crash.
4. All 376 benchmarks, timeout 30 s, tags `handover-default-t30` and `handover-dl-t30` (`-dl`).

## Failures
Exactly one, in step 3:

* `FAIL [elim-inp-gc] stress configuration: 1 of 25 search instances timed out (limit 2%)`.
  The row is `--elim --elimint=1 --elimbound=16 --reduceint=2 --tier1glue=0 --tier2glue=0 --gcfrac=0 --rootsimpdelay=0`
  (tests/matrix.txt line 107). Not a wrong answer: a solver timeout (20 s) on a search-tier instance.
  Reproduce: `tests/regress.sh -s 1:50 -M elim-inp-gc -S -j 24 BUILD/miniQU` (the instance is not named in the log; it is
  one of search seeds 26..50, found with `tests/corpus.py` of that run).

Warnings only (not failures; solver timeouts below the row limit or checker timeouts): noearly 5 solver timeouts,
restart-dl 1, restart-mode1-dl 2, ema-stress-dl 1, elim-noearly 4; in some rows proof checks timed out
(mode1-dl 3, one more row 1; see log, lines with "proof checks timed out").

## Benchmarks (30 s, one run each)
| tag | solved | SAT | UNSAT | errors | rejected proofs |
|---|---:|---:|---:|---:|---:|
| handover-default-t30 | 132 / 376 | 82 | 50 | 0 | 0 |
| handover-dl-t30 | 144 / 376 | 80 | 64 | 0 | 0 |

Verdict check (bench/compare.py): handover-default-t30 vs baseline-t180, handover-dl-t30 vs baseline-dl-t180,
and default vs dl: **no discrepancies** on the 376 common instances (the baseline timeout is 180 s, so
many instances are unsolved in the 30 s runs; only common verdicts compared).
Proof checking was not requested for these runs.
