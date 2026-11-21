#!/bin/bash
# Run every instance of tests/regressions/ with a solver binary.
#
# Usage: tests/run_regressions.sh [-n] [-c CHECKER] SOLVER [solver options...]
#
#   -n          do not check proofs
#   -c CHECKER  Lean checker (default /home/ec2-user/qu-check/.lake/build/bin/qlrup-check)
#
# The expected verdict is part of the file name (NAME.sat.qcir, NAME.unsat.qdimacs).
# .qcir instances are also solved with -proof-binary -proof=FILE and the proof
# must be accepted with the same verdict. Exit status 1 on any failure; the
# reproducing command is printed.

CHECKER=/home/ec2-user/qu-check/.lake/build/bin/qlrup-check
PROOFS=1
while getopts "nc:" opt; do
    case $opt in
        n) PROOFS= ;;
        c) CHECKER=$OPTARG ;;
        *) sed -n '2,/^$/p' "$0" | sed 's/^# \{0,1\}//'; exit 2 ;;
    esac
done
shift $((OPTIND - 1))
[ $# -ge 1 ] || { echo "usage: $0 [-n] [-c CHECKER] SOLVER [options]"; exit 2; }
SOLVER=$(readlink -f "$1"); shift
[ -x "$SOLVER" ] || { echo "run_regressions.sh: $SOLVER is not executable"; exit 2; }
[ -z "$PROOFS" ] || [ -x "$CHECKER" ] || { echo "run_regressions.sh: checker $CHECKER not found"; exit 2; }

DIR=$(cd "$(dirname "$0")/regressions" && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
failures=0 total=0

fail() { echo "FAIL $1"; echo "  repro: $2"; failures=$((failures + 1)); }

for file in "$DIR"/*.qcir "$DIR"/*.qdimacs; do
    name=$(basename "$file")
    case $name in
        *.sat.*) expected=10; verdict=SAT; want="VERIFIED TRUE" ;;
        *.unsat.*) expected=20; verdict=UNSAT; want="VERIFIED FALSE" ;;
        *) fail "$name: no .sat. or .unsat. in the name" "rename the file"; continue ;;
    esac
    total=$((total + 1))
    timeout 60 "$SOLVER" -verb=0 "$@" "$file" > /dev/null 2>&1
    code=$?
    if [ "$code" -ne "$expected" ]; then
        fail "$name: expected $verdict (exit $expected), exit code $code" "$SOLVER -verb=0 $* $file"
        continue
    fi
    if [ -n "$PROOFS" ] && [[ $name == *.qcir ]]; then
        rm -f "$TMP/p"
        timeout 60 "$SOLVER" -verb=0 "$@" -proof-binary -proof="$TMP/p" "$file" > /dev/null 2>&1
        said=$("$CHECKER" "$file" "$TMP/p" 2>/dev/null | sed -n 's/^s //p' | head -1)
        [ "$said" = "$want" ] || fail "$name: proof not accepted (checker said '${said:-nothing}')" \
            "$SOLVER -verb=0 $* -proof-binary -proof=p $file && $CHECKER $file p"
    fi
done
echo "$total instances, $failures failures"
[ "$failures" -eq 0 ]
