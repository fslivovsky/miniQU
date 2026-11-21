#!/bin/bash
# Regression test of a miniQU solver binary.
#
# Usage: tests/regress.sh [options] SOLVER [SOLVER OPTIONS...]
#
#   -s FIRST:LAST   fuzz seeds (default 1:20)
#   -j JOBS         parallel fuzz workers (default 16, at most; seed range is split)
#   -b BASELINE     reference solver (default /home/ec2-user/miniqu-work/baseline/miniQU)
#   -c CHECKER      Lean checker (default /home/ec2-user/qu-check/.lake/build/bin/qlrup-check)
#   -P PROOF_OPTS   solver options that select proof output for proof runs
#                   (default -proof-binary)
#   -S              skip the smoke test      -F  skip the fuzzing
#   -n              no proof checking
#
# Each SOLVER OPTIONS group is one configuration; separate several
# configurations with a lone "--", e.g.
#   tests/regress.sh build/miniQU -- -no-luby -- -dl
# (the first "--" starts the first configuration; a leading configuration may
# be empty, so "tests/regress.sh build/miniQU" tests the default options only).
# Within one configuration options are plain words, as for the solver.
#
# For every configuration:
#  (a) fuzzing (tests/fuzz.sh): small instances against the brute-force
#      evaluator tests/qcir_eval.py, medium ones against the baseline solver;
#  (b) every correct fuzz instance is re-solved with proof logging and the
#      proof must be accepted by the Lean checker with the right verdict;
#  (c) bench/smoke.txt is run (bench/run.py, with proof checking) and verdicts
#      are compared with bench/smoke-expected.csv.
#
# Exit status is 1 on any wrong answer, rejected proof, solver crash, or
# disagreement; reproducing commands are printed. Timeouts only warn.
# Heavy jobs run on cores 0-63 as per the project convention.

HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(dirname "$HERE")
FIRST=1; LAST=20; JOBS=16; SKIP_SMOKE=; SKIP_FUZZ=; PROOFS=1
BASELINE=/home/ec2-user/miniqu-work/baseline/miniQU
CHECKER=/home/ec2-user/qu-check/.lake/build/bin/qlrup-check
PROOF_OPTS=-proof-binary
WORK=${REGRESS_WORK:-/home/ec2-user/miniqu-work/regress}

while getopts "s:j:b:c:P:SFn" opt; do
    case $opt in
        s) FIRST=${OPTARG%%:*}; LAST=${OPTARG##*:} ;;
        j) JOBS=$OPTARG ;;
        b) BASELINE=$OPTARG ;;
        c) CHECKER=$OPTARG ;;
        P) PROOF_OPTS=$OPTARG ;;
        S) SKIP_SMOKE=1 ;;
        F) SKIP_FUZZ=1 ;;
        n) PROOFS= ;;
        *) sed -n '2,/^$/p' "$0" | sed 's/^# \{0,1\}//'; exit 2 ;;
    esac
done
shift $((OPTIND - 1))
[ $# -ge 1 ] || { echo "usage: $0 [options] SOLVER [-- OPTIONS [-- OPTIONS]...]"; exit 2; }
SOLVER=$(readlink -f "$1"); shift
[ -x "$SOLVER" ] || { echo "regress.sh: $SOLVER is not executable"; exit 2; }
[ -x "$BASELINE" ] || { echo "regress.sh: baseline $BASELINE not found"; exit 2; }
[ -z "$PROOFS" ] || [ -x "$CHECKER" ] || { echo "regress.sh: checker $CHECKER not found"; exit 2; }

# Split the remaining arguments into configurations at each "--".
configs=()
current=
seen=
for arg in "$@"; do
    if [ "$arg" = "--" ]; then
        [ -n "$seen" ] && configs+=("$current")
        current=; seen=1
    else
        current="$current $arg"
    fi
done
if [ -n "$seen" ] || [ ${#configs[@]} -eq 0 ]; then configs+=("$current"); fi

mkdir -p "$WORK"
total_failures=0
total_warnings=0

for opts in "${configs[@]}"; do
    echo "=== configuration:${opts:- (default options)}"
    tag=$(echo "${opts:-default}" | tr -c 'A-Za-z0-9\n' '_' | sed 's/^_*//')
    run="$WORK/$tag"
    rm -rf "$run"; mkdir -p "$run"

    if [ -z "$SKIP_FUZZ" ]; then
        # Split the seed range over parallel workers.
        n=$((LAST - FIRST + 1)); [ "$n" -lt "$JOBS" ] && workers=$n || workers=$JOBS
        chunk=$(( (n + workers - 1) / workers ))
        pids=()
        for ((w = 0; w < workers; w++)); do
            lo=$((FIRST + w * chunk)); hi=$((lo + chunk - 1)); [ "$hi" -gt "$LAST" ] && hi=$LAST
            [ "$lo" -gt "$LAST" ] && break
            env REFERENCE="$BASELINE" KEEP_DIR="$run/failed" ${PROOFS:+PROOF_CHECKER="$CHECKER"} PROOF_OPTS="$PROOF_OPTS" \
                taskset -c 0-63 "$HERE/fuzz.sh" "$SOLVER" "$lo" "$hi" $opts > "$run/fuzz-$lo-$hi.log" 2>&1 &
            pids+=($!)
        done
        fuzz_failed=0
        for pid in "${pids[@]}"; do wait "$pid" || fuzz_failed=1; done
        cat "$run"/fuzz-*.log | grep -v '^[0-9]* failures' | sed 's/^/    /'
        sum=$(cat "$run"/fuzz-*.log | sed -n 's/^\([0-9]*\) failures, \([0-9]*\) timeouts, \([0-9]*\) proofs checked, \([0-9]*\) proof.*/\1 \2 \3 \4/p' |
              awk '{f+=$1; t+=$2; p+=$3; q+=$4} END {print f+0, t+0, p+0, q+0}')
        set -- $sum
        echo "  fuzz seeds $FIRST..$LAST: $1 failures, $2 timeouts, $3 proofs checked ($4 checks timed out: warning only)"
        total_failures=$((total_failures + $1))
        total_warnings=$((total_warnings + $2))
        # A worker that died without printing a summary line is also a failure.
        if [ "$fuzz_failed" = 1 ] && [ "$1" -eq 0 ]; then
            echo "  fuzz worker exited abnormally; see $run/fuzz-*.log"
            total_failures=$((total_failures + 1))
        fi
    fi

    if [ -z "$SKIP_SMOKE" ]; then
        # The solver options are passed as one quoted string; options with spaces are unsupported.
        python3 "$REPO/bench/run.py" --solver "$SOLVER" --args="$opts" --tag "regress-$tag" \
            --results-dir "$run/results" --timeout 120 --jobs "$JOBS" --cores 0-63 \
            --instances "$REPO/bench/smoke.txt" --proof-jobs "$JOBS" --proof-args="$PROOF_OPTS" \
            --checker "$CHECKER" ${PROOFS:+--proof-check --proof-max-solve-sec 60} \
            > "$run/smoke.log" 2>&1
        smoke_status=$?
        python3 - "$run/results/regress-$tag/results.csv" "$REPO/bench/smoke-expected.csv" <<'EOF' | sed 's/^/    /'
import csv, sys
got = {r["instance"]: r for r in csv.DictReader(open(sys.argv[1]))}
bad = warn = 0
for r in csv.DictReader(open(sys.argv[2])):
    g = got.get(r["instance"])
    if g is None:
        print("FAIL smoke: %s missing from results" % r["instance"]); bad += 1
    elif g["result"] in ("SAT", "UNSAT") and g["result"] != r["result"]:
        print("FAIL smoke: %s expected %s, got %s" % (r["instance"], r["result"], g["result"])); bad += 1
    elif g["result"] in ("ERROR", "MISMATCH", "MEMOUT"):
        print("FAIL smoke: %s result %s (exit %s)" % (r["instance"], g["result"], g["exit"])); bad += 1
    elif g["result"] == "TIMEOUT":
        print("WARN smoke: %s timed out" % r["instance"]); warn += 1
    if g and g["proof_status"] not in ("", "n/a", "ok"):
        print("FAIL smoke: proof of %s: %s" % (r["instance"], g["proof_status"])); bad += 1
print("smoke: %d failures, %d timeouts" % (bad, warn))
sys.exit(1 if bad else 0)
EOF
        py=${PIPESTATUS[0]}
        if [ "$py" -ne 0 ] || [ "$smoke_status" -ne 0 ]; then
            echo "  smoke test FAILED; log $run/smoke.log"
            echo "  repro: python3 bench/run.py --solver $SOLVER --args '$opts' --tag t --instances bench/smoke.txt --proof-check"
            total_failures=$((total_failures + 1))
        fi
    fi
done

echo
if [ "$total_failures" -eq 0 ]; then
    echo "REGRESSION TESTS PASSED ($total_warnings timeouts)"
    exit 0
fi
echo "REGRESSION TESTS FAILED: $total_failures problem(s)"
exit 1
