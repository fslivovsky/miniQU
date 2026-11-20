#!/bin/bash
# Fuzz a miniQU binary on random QCIR instances.
#
# Usage: tests/fuzz.sh BINARY FIRST_SEED LAST_SEED [solver options...]
#
# Small instances are checked against a brute-force evaluator. If the
# environment variable REFERENCE names another solver binary, medium-sized
# instances are additionally checked against its result (run with "-dl").
# Instances on which either solver exceeds TIMEOUT seconds (default 20) are
# counted separately. Prints failing instances and exits with status 1 if
# there was any failure.

BINARY=$1; FIRST=$2; LAST=$3; shift 3
DIR=$(dirname "$0")
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
failures=0
timeouts=0

solve() {  # solve BINARY FILE [options...] -> SAT, UNSAT or an error description
    local binary=$1 file=$2; shift 2
    timeout "${TIMEOUT:-20}" "$binary" -verb=0 "$@" "$file" > /dev/null 2>&1
    local code=$?
    case $code in
        10)  echo SAT ;;
        20)  echo UNSAT ;;
        124) echo TIMEOUT ;;
        *)   echo "exit code $code" ;;
    esac
}

check() {  # check DESCRIPTION EXPECTED [options...]
    local description=$1 expected=$2; shift 2
    local result
    result=$(solve "$BINARY" "$TMP/f.qcir" "$@")
    if [ "$result" = TIMEOUT ] || [ "$expected" = TIMEOUT ]; then
        timeouts=$((timeouts + 1))
    elif [ "$result" != "$expected" ]; then
        echo "FAIL $description: expected $expected, got $result"
        failures=$((failures + 1))
    fi
}

for seed in $(seq "$FIRST" "$LAST"); do
    for flags in "" "--cnf" "--vars 16 --gates 60 --blocks 8"; do
        python3 "$DIR/qcir_fuzz.py" "$seed" $flags > "$TMP/f.qcir"
        check "qcir_fuzz.py $seed $flags" "$(sed -n 's/^# expected: //p' "$TMP/f.qcir")" "$@"
    done
    for instance in "qcnf $seed 5 5" "qcnf $seed 6 6" "qcnf $seed 7 7" "reach $seed 6 8" \
                    "reach $seed 7 12" "reach $seed 8 16" "game $seed 5" "synth $seed 8"; do
        python3 "$DIR/qcir_gen.py" $instance > "$TMP/f.qcir"
        check "qcir_gen.py $instance" "$(python3 "$DIR/qcir_eval.py" "$TMP/f.qcir")" "$@"
    done
    if [ -n "$REFERENCE" ]; then
        for instance in "qcnf $seed 40 5" "qcnf $seed 60 5.5" "reach $seed 15 16" "reach $seed 19 12" \
                        "game $seed 30" "synth $seed 25"; do
            python3 "$DIR/qcir_gen.py" $instance > "$TMP/f.qcir"
            check "qcir_gen.py $instance" "$(solve "$REFERENCE" "$TMP/f.qcir" -dl)" "$@"
        done
    fi
done
echo "$failures failures, $timeouts timeouts"
[ "$failures" -eq 0 ]
