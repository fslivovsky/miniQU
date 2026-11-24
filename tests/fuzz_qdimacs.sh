#!/bin/bash
# Fuzz a miniQU binary on random QDIMACS instances (qbfuzz.py).
#
# Usage: tests/fuzz_qdimacs.sh SOLVER FIRST_SEED LAST_SEED [solver options...]
#
# Solver options are separate arguments (... -dl --reduceint=2); an argument
# with whitespace is a quoted option string, which would reach the solver as
# one unknown option, so the script rejects it with exit status 2.
#
# Per seed there are two instances:
#   tiny   few enough variables for the brute-force evaluator (tests/qcir_eval.py)
#   large  prenex 4-CNF that needs roughly 10^2 to 10^4 conflicts of the baseline
# For each, SOLVER on the .qdimacs file, SOLVER on the tests/qdimacs2qcir.py
# conversion, and the baseline on the .qdimacs file must agree (and with the
# evaluator on the tiny one). Prints every disagreement or crash (exit code
# other than 10/20) with a reproducing command; exits with status 1 if there
# was any. Instances that exceed TIMEOUT seconds (default 20) are only counted.
#
# Environment: BASELINE (default /home/ec2-user/miniqu-work/baseline/miniQU),
# KEEP_DIR (directory in which failing instances are saved).

SOLVER=$1; FIRST=$2; LAST=$3; shift 3
for option in "$@"; do
    case $option in
        *[[:space:]]*)
            echo "fuzz_qdimacs.sh: option '$option' contains whitespace; pass options as separate arguments, e.g. $0 SOLVER 1 10 -dl --reduceint=2, not \"-dl --reduceint=2\"" >&2
            exit 2 ;;
    esac
done
DIR=$(dirname "$0")
BASELINE=${BASELINE:-/home/ec2-user/miniqu-work/baseline/miniQU}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
failures=0
timeouts=0
checked=0

TINY="-v 14 -c 50 -s 4 -r 0.6 --min=2 --max=4"
LARGE="-v 70 -c 300 -s 3 -r 0.8 --min=4 --max=4"

solve() {  # solve BINARY FILE [options...] -> SAT, UNSAT, TIMEOUT or an error description
    local binary=$1 file=$2; shift 2
    timeout "${TIMEOUT:-20}" "$binary" -verb=0 "$@" "$file" > /dev/null 2>&1
    case $? in
        10)  echo SAT ;;
        20)  echo UNSAT ;;
        124) echo TIMEOUT ;;
        *)   echo "exit code $?" ;;
    esac
}

fail() {  # fail MESSAGE REPRO: report a failure and save the instance
    echo "FAIL $1"
    echo "  repro: $2"
    if [ -n "$KEEP_DIR" ]; then
        mkdir -p "$KEEP_DIR"
        cp "$TMP/f.qdimacs" "$KEEP_DIR/fail-$failures.qdimacs" && echo "  saved: $KEEP_DIR/fail-$failures.qdimacs"
    fi
    failures=$((failures + 1))
}

check() {  # check SEED KIND GENERATOR_OPTIONS [solver options...]
    local seed=$1 kind=$2 generator=$3; shift 3
    local gen="python3 $DIR/../qbfuzz.py --seed=$seed $generator -o f.qdimacs"
    python3 "$DIR/../qbfuzz.py" --seed="$seed" $generator -o "$TMP/f.qdimacs" > /dev/null
    python3 "$DIR/qdimacs2qcir.py" "$TMP/f.qdimacs" > "$TMP/f.qcir"
    local direct converted reference truth=
    direct=$(solve "$SOLVER" "$TMP/f.qdimacs" "$@")
    converted=$(solve "$SOLVER" "$TMP/f.qcir" "$@")
    reference=$(solve "$BASELINE" "$TMP/f.qdimacs")
    [ "$kind" = tiny ] && truth=$(python3 "$DIR/qcir_eval.py" "$TMP/f.qcir")
    local repro="$gen && python3 $DIR/qdimacs2qcir.py f.qdimacs > f.qcir && $SOLVER -verb=0 $* f.qdimacs; $SOLVER -verb=0 $* f.qcir"
    local summary=".qdimacs says $direct, converted .qcir says $converted, baseline says $reference${truth:+, evaluator says $truth}"
    local finished=()
    for result in "$direct" "$converted" "$reference" $truth; do
        case $result in
            SAT|UNSAT) finished+=("$result") ;;
            TIMEOUT) ;;
            *) fail "$kind seed $seed: crash ($summary)" "$repro"; return ;;
        esac
    done
    if [ "$direct" = TIMEOUT ] || [ "$converted" = TIMEOUT ]; then
        timeouts=$((timeouts + 1))
    elif [ "$(printf '%s\n' "${finished[@]}" | sort -u | wc -l)" -ne 1 ]; then
        fail "$kind seed $seed: $summary" "$repro"
    else
        checked=$((checked + 1))
    fi
}

for seed in $(seq "$FIRST" "$LAST"); do
    check "$seed" tiny "$TINY" "$@"
    check "$seed" large "$LARGE" "$@"
done
echo "$failures failures, $timeouts timeouts, $checked instances agreed"
[ "$failures" -eq 0 ]
