#!/bin/bash
# Regression test of a miniQU solver binary.
#
# Usage: tests/regress.sh [options] SOLVER [-- SOLVER OPTIONS]...
#
#   -s FIRST:LAST   corpus seeds (default 1:20); the first half of the range
#                   is run on the tiny tier, the second half on the search tier
#   -M ROWS         run these rows of the configuration matrix (comma-separated
#                   names, or "all") instead of "--" groups
#   -m FILE         matrix file (default tests/matrix.txt); implies -M all
#   -j JOBS         parallel workers (default 16, at most)
#   -b BASELINE     reference solver (default /home/ec2-user/miniqu-work/baseline/miniQU)
#   -c CHECKER      Lean checker (default /home/ec2-user/qu-check/.lake/build/bin/qlrup-check)
#   -P PROOF_OPTS   solver options that select proof output for proof runs
#                   (default -proof-binary; the file is added as -proof=FILE)
#   -t SECONDS      solver timeout per run (default 20)
#   -S              skip the smoke test      -F  skip the corpus runs
#   -n              no proof checking
#
# Explicit configurations: each group of SOLVER OPTIONS after a lone "--" is
# one configuration, e.g.
#   tests/regress.sh build/miniQU -- -no-luby -- -dl
# (a leading group may be empty; "tests/regress.sh build/miniQU" tests the
# default options only). They have no required counters.
#
# For every configuration (engine: tests/regress.py, corpus: tests/corpus.py):
#  (a) tiny tier: verdicts against the brute-force evaluator; search tier:
#      verdicts against the baseline solver, and across the configurations of
#      one invocation;
#  (b) every correct verdict is re-solved with proof logging and the proof must
#      be accepted by the Lean checker with the right verdict (rows with
#      proofs "yes");
#  (c) coverage assertion: the search tier is run with -verb=1; lines
#      "c stat NAME INTEGER" are summed; a counter required by the row that is
#      nonzero on fewer than 10% of the finished instances fails the run. An
#      explicit "--" group whose solver prints no such line is exempt (old
#      interface); a matrix row is not;
#  (d) timeouts are counted per configuration; more than the row's limit (sixth
#      field of tests/matrix.txt, default 2%) on the search tier fails a stress
#      row, otherwise they only warn;
#  (e) bench/smoke.txt is run with bench/run.py and compared with
#      bench/smoke-expected.csv.
#
# Exit status is 1 on any wrong verdict, rejected proof, crash (exit code other
# than 10/20), failed assertion; reproducing commands are printed.
# Heavy jobs run on cores 0-63 as per the project convention.

HERE=$(cd "$(dirname "$0")" && pwd)
SEEDS=1:20; JOBS=16; MATRIX=; ROWS=; TIMEOUT=20
BASELINE=/home/ec2-user/miniqu-work/baseline/miniQU
CHECKER=/home/ec2-user/qu-check/.lake/build/bin/qlrup-check
PROOF_OPTS=-proof-binary
WORK=${REGRESS_WORK:-/home/ec2-user/miniqu-work/regress}
engine_flags=()

while getopts "s:M:m:j:b:c:P:t:SFn" opt; do
    case $opt in
        s) SEEDS=$OPTARG ;;
        M) ROWS=$OPTARG ;;
        m) MATRIX=$OPTARG ;;
        j) JOBS=$OPTARG ;;
        b) BASELINE=$OPTARG ;;
        c) CHECKER=$OPTARG ;;
        P) PROOF_OPTS=$OPTARG ;;
        t) TIMEOUT=$OPTARG ;;
        S) engine_flags+=(--no-smoke) ;;
        F) engine_flags+=(--no-fuzz) ;;
        n) engine_flags+=(--no-proofs); NO_PROOFS=1 ;;
        *) sed -n '2,/^$/p' "$0" | sed 's/^# \{0,1\}//'; exit 2 ;;
    esac
done
shift $((OPTIND - 1))
[ $# -ge 1 ] || { echo "usage: $0 [options] SOLVER [-- OPTIONS [-- OPTIONS]...]"; exit 2; }
SOLVER=$(readlink -f "$1"); shift
[ -x "$SOLVER" ] || { echo "regress.sh: $SOLVER is not executable"; exit 2; }
[ -x "$BASELINE" ] || { echo "regress.sh: baseline $BASELINE not found"; exit 2; }
[ -n "$NO_PROOFS" ] || [ -x "$CHECKER" ] || { echo "regress.sh: checker $CHECKER not found"; exit 2; }

if [ -n "$MATRIX$ROWS" ]; then
    [ $# -eq 0 ] || { echo "regress.sh: -M/-m and '--' groups cannot be combined"; exit 2; }
    engine_flags+=(--matrix "${MATRIX:-$HERE/matrix.txt}" --rows "${ROWS:-all}")
else
    # Split the remaining arguments into configurations at each "--".
    current=; seen=; groups=()
    for arg in "$@"; do
        if [ "$arg" = "--" ]; then
            [ -n "$seen" ] && groups+=("$current")
            current=; seen=1
        else
            current="$current $arg"
        fi
    done
    if [ -n "$seen" ] || [ ${#groups[@]} -eq 0 ]; then groups+=("$current"); fi
    for g in "${groups[@]}"; do engine_flags+=(--group="$g"); done
fi

mkdir -p "$WORK"
exec taskset -c 0-63 python3 "$HERE/regress.py" --solver "$SOLVER" --baseline "$BASELINE" \
    --checker "$CHECKER" --seeds "$SEEDS" --jobs "$JOBS" --timeout "$TIMEOUT" \
    --proof-opts="$PROOF_OPTS" --work "$WORK" "${engine_flags[@]}"
