# M4 sanity run (vivification on real benchmark files)

This is a SANITY run, not a benchmark: single seed, one run per cell, jobs not pinned to the benchmark
cores (cores 24-47 of a 48-core machine, 16 in parallel, other work ran on cores 0-23), no timing
comparison, no conclusion about speed. Its only purpose is to catch wrong verdicts and rejected proofs.

- Binary: release build of branch rewrite/cadical-style after M4-T2 (commit f2668b7), `-verb=1`.
- Instances: 12 files of /home/ec2-user/benchmarks/qcir taken from `bench/results/baseline-t180/results.csv`
  (solved by the baseline in under 30 s, 6 SAT and 6 UNSAT by that file).
- Configurations: default; `--vivify`; `--vivify -dl`; `--vivify --elim`;
  `--vivify --vivifytier=3 --vivifyint=500`. Each: `timeout 120`, `ulimit -v 8388608`, `taskset -c 24-47`.
- Verdicts of all 60 runs equal the default run and the verdict of `baseline-t180` (66 rows incl. proof runs, 0 mismatches).
- `lean_check`: the 6 fastest instances were re-run with `--vivify --proof=FILE --proofbinary` and the proof
  checked with `/home/ec2-user/qu-check/.lake/build/bin/qlrup-check FORMULA PROOF` (6/6 verified, proofs deleted).
- Columns: wall time and the counters `conflicts`, `vivifyrounds`, `vivifychecked.*`, `vivified.*`,
  `vivifiedlits.*`, `vivifyunits` from the `c stat` lines. Wall time includes parsing; times are not comparable
  with other machines or other harness settings. Many instances finish before the first round (`vivifyint` 2000).
- Scripts (not kept in the repo): `/home/ec2-user/miniqu-work/m4t3/{one.sh,parse.py}`, logs `m4t3/runs/`.
