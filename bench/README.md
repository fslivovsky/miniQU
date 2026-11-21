# Benchmark and regression tooling

Python 3 standard library only. All large artifacts live in
`/home/ec2-user/miniqu-work` (outside the repo); only small CSV/markdown results
are committed under `bench/results/TAG/`.

## Layout of /home/ec2-user/miniqu-work

| path | content |
|---|---|
| `baseline-src/` | git worktree of commit c39005a (frozen reference sources) |
| `baseline-build/` | CMake release build tree of the baseline |
| `baseline/miniQU`, `baseline/GIT_HASH` | the frozen reference binary. Never rebuild it from changed sources. |
| `proofs/` | temporary proof files (deleted after checking) |
| `logs/` | logs of failed runs, build logs |
| `regress/` | scratch space of tests/regress.sh |

Rebuild from scratch:

    cd /home/ec2-user/miniQU && git checkout rewrite/cadical-style   # created from c39005a
    mkdir -p /home/ec2-user/miniqu-work/{logs,proofs,baseline}
    git worktree add /home/ec2-user/miniqu-work/baseline-src c39005a   # detached
    cmake -S /home/ec2-user/miniqu-work/baseline-src -B /home/ec2-user/miniqu-work/baseline-build -DCMAKE_BUILD_TYPE=Release
    taskset -c 0-63 make -C /home/ec2-user/miniqu-work/baseline-build -j16
    cp /home/ec2-user/miniqu-work/baseline-build/miniQU /home/ec2-user/miniqu-work/baseline/miniQU
    echo c39005a > /home/ec2-user/miniqu-work/baseline/GIT_HASH
    # Lean checker (nothing of Mathlib is compiled, only downloaded)
    cd /home/ec2-user/qu-check && git submodule update --init && taskset -c 0-63 lake build
    # binary: /home/ec2-user/qu-check/.lake/build/bin/qlrup-check [--stats] FORMULA.qcir PROOF
    # (its own test.sh also works)

Benchmarks: `/home/ec2-user/benchmarks/qcir` (376 .qcir files, from ~/benchmarks/qcir.zip).

## Core convention

Timed benchmark jobs run on cores 64-127, one core per job (`taskset`). Every
other heavy command (builds, fuzzing, proof checking) is prefixed with
`taskset -c 0-63` and uses at most ~16 parallel jobs. run.py's proof phase and
tests/regress.sh follow this by default.

## run.py

    python3 bench/run.py --solver PATH --args "-opt1 -opt2" --tag TAG --timeout 300 \
        [--jobs 48] [--cores 64-127] [--mem-gb 8] [--instances GLOB|FILE.txt|NAMES...] \
        [--proof-check [--proof-max-solve-sec 20] [--proof-timeout 600]]

* Each instance runs once, pinned to one core; wall time, CPU time and peak RSS
  are recorded. Timeout (wall) and memory limit (RSS) are enforced by killing
  the process group.
* Verdict: exit code 10 = SAT, 20 = UNSAT, cross-checked with the printed
  `SATISFIABLE`/`UNSATISFIABLE` line (disagreement gives result `MISMATCH`).
  Other results: `TIMEOUT`, `MEMOUT`, `ERROR`.
* Output: `bench/results/TAG/results.csv`
  (instance,family,result,exit,wall,cpu,rss_mb,proof_status,proof_check_sec,proof_bytes)
  and `meta.json` (solver path, sha256 and git hash, args, date, host, timeout,
  command line). Resumable: rerunning with the same tag skips instances already
  in the CSV (delete the directory for a fresh run).
* `--proof-check`: after the timed phase, instances solved in at most
  `--proof-max-solve-sec` are re-run with `-proof=/home/ec2-user/miniqu-work/proofs/...`
  (extra options `--proof-args`, default `-proof-binary`), the proof is checked with
  qlrup-check (limit `--proof-timeout`) and deleted. `proof_status` is `ok`,
  `rejected`, `wrong_verdict`, `check_timeout`, `check_memout`, `check_error`, `solve_*` (proof run did not finish), or `n/a` when not attempted.
  Proof phase runs on `--proof-cores` (default 0-63, `--proof-jobs` 16).
* `--instances` takes globs relative to `--bench-dir`, paths, or a `.txt` list of names
  (lines starting with `#` are comments). Options whose value starts with `-` must be written
  `--args=-opt` (argparse).

Example, full run of a solver with proof checking:

    nohup setsid python3 bench/run.py --solver build/miniQU --tag new-default --timeout 300 \
        --proof-check > /home/ec2-user/miniqu-work/logs/new-default.log 2>&1 &

## compare.py

    python3 bench/compare.py TAG_A TAG_B [TAG_C ...] [--out FILE] [--cactus FILE.csv] [--top 10]

Markdown report: result DISCREPANCIES and errors first (blocking bugs), solved
SAT/UNSAT/total, PAR2 (penalty 2x timeout), unique solves, per-family table,
top speedups/regressions relative to the first tag, proof-check statistics,
and cactus data (sorted solve times per tag) as CSV. Only instances present in every run are compared; a warning is
printed when the timeouts differ. Family = leading alphabetic prefix of the file name
(`chess`, `ci`, `klieber`, ...); names starting with a digit form `numeric`.

## smoke.txt

35 instances (33 names) that the baseline solves in under 3 s (mixed families, SAT and UNSAT).
`smoke-expected.csv` holds the verdicts (from the baseline, cross-checked by its
proofs). Reference results: `results/baseline-smoke` (with proof checking, all 33 proofs ok)
and `results/baseline-t5` (all 376 instances, 5 s timeout, used to choose the subset).

## tests/regress.sh

    tests/regress.sh [-s FIRST:LAST] [-j JOBS] [-n] [-S] [-F] SOLVER [-- OPTS [-- OPTS ...]]
    tests/regress.sh build/miniQU -- -no-luby -- -dl      # two configurations

Each `--` starts a configuration (a bare `SOLVER` tests default options only; with
a leading `--` the first configuration is the options after it). For every configuration:

1. tests/fuzz.sh: generators qcir_fuzz.py / qcir_gen.py; small instances are compared with the brute-force
   `tests/qcir_eval.py`, medium ones with the baseline binary (`-b`);
2. every correct fuzz instance is re-solved with proof logging and checked by the Lean checker
   (verdict must match; checker time-outs are counted as warnings only);
3. bench/smoke.txt through run.py with proof checking, compared with smoke-expected.csv.

Exit status 1 on any wrong answer, crash, rejected proof or disagreement; reproducing
commands are printed and failing instances saved in `/home/ec2-user/miniqu-work/regress/CONFIG/failed/`.
Solver timeouts only warn. `tests/fuzz.sh` can also be used alone
(`PROOF_CHECKER=... REFERENCE=baseline tests/fuzz.sh SOLVER FIRST LAST [opts]`).
