#!/bin/bash
# Fuzz a miniQU binary on random QCIR instances.
#
# Usage: tests/fuzz.sh BINARY FIRST_SEED LAST_SEED [solver options...]
#
# Small instances are checked against a brute-force evaluator. If the
# environment variable REFERENCE names another solver binary, medium-sized
# instances are additionally checked against its result (run with "-dl").
# Instances on which either solver exceeds TIMEOUT seconds (default 20) are
# counted separately. Prints failing instances, with a command that reproduces
# each failure, and exits with status 1 if there was any failure.
#
# Optional environment variables:
#   PROOF_CHECKER  path of the Lean checker (qlrup-check); if set, every instance
#                  whose result is correct is re-solved with -proof=FILE and the
#                  proof must be accepted with the matching verdict (TRUE for SAT,
#                  FALSE for UNSAT).
#   PROOF_OPTS     extra solver options for proof runs (default: -proof-binary)
#   KEEP_DIR       directory in which failing instances are saved

BINARY=$1; FIRST=$2; LAST=$3; shift 3
DIR=$(dirname "$0")
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
failures=0
timeouts=0
proofs=0
proof_timeouts=0
GENERATOR=       # command line that regenerates the current instance

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

fail() {  # fail MESSAGE [options...]: report a failure with a reproducing command
    local message=$1; shift
    echo "FAIL $message"
    echo "  repro: python3 $DIR/$GENERATOR > f.qcir && $BINARY -verb=0 $* f.qcir"
    if [ -n "$KEEP_DIR" ]; then
        mkdir -p "$KEEP_DIR"
        local kept="$KEEP_DIR/fail-$(date +%s)-$failures.qcir"
        cp "$TMP/f.qcir" "$kept" && echo "  saved: $kept"
    fi
    failures=$((failures + 1))
}

check_proof() {  # check_proof EXPECTED [options...]
    local expected=$1; shift
    local verdict
    timeout "${TIMEOUT:-20}" "$BINARY" -verb=0 "$@" ${PROOF_OPTS--proof-binary} -proof="$TMP/f.proof" \
        "$TMP/f.qcir" > /dev/null 2>&1
    if [ ! -s "$TMP/f.proof" ]; then
        rm -f "$TMP/f.proof"; return  # solver timed out or wrote no proof; not a failure
    fi
    proofs=$((proofs + 1))
    local out status
    out=$(timeout "${CHECK_TIMEOUT:-120}" "$PROOF_CHECKER" "$TMP/f.qcir" "$TMP/f.proof" 2>/dev/null)
    status=$?
    rm -f "$TMP/f.proof"
    if [ "$status" -eq 124 ]; then  # the checker ran out of time: a warning, not a verdict
        proof_timeouts=$((proof_timeouts + 1)); proofs=$((proofs - 1)); return
    fi
    verdict=$(echo "$out" | sed -n 's/^s //p' | head -1)
    local want="VERIFIED TRUE"
    [ "$expected" = UNSAT ] && want="VERIFIED FALSE"
    if [ "$verdict" != "$want" ]; then
        fail "proof for $GENERATOR rejected or wrong: expected '$want', checker said '${verdict:-nothing}'" \
            "$@" ${PROOF_OPTS--proof-binary} -proof=f.proof
    fi
}

check() {  # check DESCRIPTION EXPECTED [options...]
    local description=$1 expected=$2; shift 2
    local result
    GENERATOR=$description
    result=$(solve "$BINARY" "$TMP/f.qcir" "$@")
    if [ "$result" = TIMEOUT ] || [ "$expected" = TIMEOUT ]; then
        timeouts=$((timeouts + 1))
    elif [ "$result" != "$expected" ]; then
        fail "$description: expected $expected, got $result" "$@"
    elif [ -n "$PROOF_CHECKER" ]; then
        check_proof "$expected" "$@"
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
echo "$failures failures, $timeouts timeouts, $proofs proofs checked, $proof_timeouts proof checks timed out"
[ "$failures" -eq 0 ]
