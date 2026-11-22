#!/bin/bash
# Validate the certificates (-cert) of a solver on generated instances.
#
# Usage: tests/fuzz_cert.sh SOLVER FIRST_SEED LAST_SEED [solver options...]
#
# Per seed there are four instances: the tiny and the search tier of
# tests/corpus.py (QCIR) and a tiny and a large QDIMACS instance of qbfuzz.py
# (the parameters of tests/fuzz_qdimacs.sh).  Each is checked with
# tests/check_cert.py, which substitutes the certificate into the formula and
# decides the result again (see there for the statuses).  Prints the number of
# instances per status, and for INVALID, MALFORMED and ERROR the three smallest
# instances with the command that reproduces them; all of them are saved in
# KEEP_DIR.  Exit status 1 if there is any INVALID, MALFORMED or ERROR.
#
# Environment: JOBS (parallel checks, default 12), KEEP_DIR (default
# /home/ec2-user/miniqu-work/cert/BINARY-NAME-OPTIONS), TIMEOUT (per solver
# run, default 60), BASELINE (reference solver for the large instances).
# Heavy jobs belong on cores 0-63: run it under taskset -c 0-63.

SOLVER=$(readlink -f "$1"); FIRST=$2; LAST=$3; shift 3
DIR=$(cd "$(dirname "$0")" && pwd)
BASELINE=${BASELINE:-/home/ec2-user/miniqu-work/baseline/miniQU}
JOBS=${JOBS:-12}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
LABEL=$(basename "$(dirname "$SOLVER")")-$(basename "$SOLVER")$(printf '%s' "$*" | tr -c 'A-Za-z0-9=' '_')
KEEP_DIR=${KEEP_DIR:-/home/ec2-user/miniqu-work/cert/$LABEL}

TINY="-v 14 -c 50 -s 4 -r 0.6 --min=2 --max=4"
LARGE="-v 70 -c 300 -s 3 -r 0.8 --min=4 --max=4"
mkdir -p "$TMP/in"
for seed in $(seq "$FIRST" "$LAST"); do
    python3 "$DIR/corpus.py" --tier tiny --seed "$seed" --out "$TMP/in/tiny-$seed.qcir" 2> /dev/null
    python3 "$DIR/corpus.py" --tier search --seed "$seed" --out "$TMP/in/search-$seed.qcir" 2> /dev/null
    python3 "$DIR/../qbfuzz.py" --seed="$seed" $TINY -o "$TMP/in/qdimacs-tiny-$seed.qdimacs" > /dev/null
    python3 "$DIR/../qbfuzz.py" --seed="$seed" $LARGE -o "$TMP/in/qdimacs-large-$seed.qdimacs" > /dev/null
done

ls "$TMP/in" | xargs -P "$JOBS" -I{} \
    python3 "$DIR/check_cert.py" --reference "$BASELINE" --timeout "${TIMEOUT:-60}" \
    "$SOLVER" "$TMP/in/{}" "$@" > "$TMP/results.txt"

echo "certificates of $SOLVER $* on seeds $FIRST:$LAST"
awk '{count[$1]++} END {for (s in count) printf "  %-10s %d\n", s, count[s]}' "$TMP/results.txt" | sort
bad=$(grep -cE '^(INVALID|MALFORMED|ERROR) ' "$TMP/results.txt")
if [ "$bad" -gt 0 ]; then
    mkdir -p "$KEEP_DIR"
    grep -E '^(INVALID|MALFORMED|ERROR) ' "$TMP/results.txt" | while read -r status file detail; do
        cp "$file" "$KEEP_DIR/"
        echo "$status $(basename "$file") $(stat -c %s "$file") $detail"
    done | sort -k3,3n > "$KEEP_DIR/bad.txt"
    echo "bad certificates (smallest three of $bad; all in $KEEP_DIR, list in bad.txt):"
    head -3 "$KEEP_DIR/bad.txt" | while read -r status name size detail; do
        echo "  $status $name ($size bytes): $detail"
        echo "    repro: python3 $DIR/check_cert.py $SOLVER $KEEP_DIR/$name $*"
    done
fi
[ "$bad" -eq 0 ]
