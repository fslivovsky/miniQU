#!/bin/bash
# Compare the encoding of the new frontend with the baseline's.
#
# Usage: tests/encoding_diff.sh FIRST LAST [FILE.qcir ...]
#
# For the seeds FIRST..LAST the instances of both tiers of tests/corpus.py are
# generated; the instances of tests/regressions/ and the FILEs given on the
# command line are checked as well.  Each instance is encoded by encoding-dump
# and solved by the baseline with a text proof; the multiset of the constraints
# (kind, gate, sorted literals in proof numbers) must equal the multiset of the
# 'o' lines of the proof, with early Tseitin variables on and off.  Any
# difference is a failure and is printed with the command that reproduces it.
#
# The baseline writes the 'o' lines while it parses, so it is interrupted as
# soon as it reports its parse time (SIGINT makes it close the proof) instead
# of solving the instance.
#
# Environment: BASELINE (baseline binary), ENCODING_DUMP (the tool built by
# CMake), JOBS (parallel checks, default 16), BASELINE_TIMEOUT (seconds the
# baseline may take to parse, default 60; exceeding it is a failure).

BASELINE=${BASELINE:-/home/ec2-user/miniqu-work/baseline/miniQU}
DUMP=${ENCODING_DUMP:-/home/ec2-user/miniqu-work/build/release/encoding-dump}
JOBS=${JOBS:-16}
BASELINE_TIMEOUT=${BASELINE_TIMEOUT:-60}
HERE=$(cd "$(dirname "$0")" && pwd)

[ $# -ge 2 ] || { sed -n '2,/^$/p' "$0" | sed 's/^# \{0,1\}//'; exit 2; }
FIRST=$1 LAST=$2
shift 2
[ -x "$BASELINE" ] || { echo "encoding_diff.sh: baseline $BASELINE not found"; exit 2; }
[ -x "$DUMP" ] || { echo "encoding_diff.sh: $DUMP not found"; exit 2; }

mkdir -p /home/ec2-user/miniqu-work
TMP=$(mktemp -d /home/ec2-user/miniqu-work/encdiff.XXXXXX)
trap 'rm -rf "$TMP"' EXIT

# The 'o' lines of a text proof as "o KIND GATE LITS", literals sorted.
baseline_constraints() {
    python3 -I -c '
import sys
for line in open(sys.argv[1]):
    f = line.split()
    if f and f[0] == "o":
        lits = sorted(int(x) for x in f[4:-1])
        print("o", f[2], f[3], *lits)
' "$1" | LC_ALL=C sort
}

# run_baseline FILE FLAG PROOF: runs the baseline until it has parsed FILE.
run_baseline() {
    local out=$TMP/stdout.$BASHPID waited=0
    : > "$out"
    stdbuf -oL "$BASELINE" -verb=1 $2 -proof="$3" "$1" > "$out" 2> /dev/null &
    local pid=$!
    while kill -0 $pid 2> /dev/null && ! grep -q 'Parse time' "$out"; do
        sleep 0.05
        waited=$((waited + 1))
        if [ $waited -gt $((BASELINE_TIMEOUT * 20)) ]; then
            kill -KILL $pid; wait $pid 2> /dev/null; rm -f "$out"
            return 1
        fi
    done
    kill -INT $pid 2> /dev/null
    for _ in $(seq 200); do
        kill -0 $pid 2> /dev/null || break
        sleep 0.1
    done
    kill -KILL $pid 2> /dev/null
    wait $pid 2> /dev/null
    rm -f "$out"
    return 0
}

# check FILE: prints one block per difference, nothing if the file agrees.  A
# failing file is kept in $KEEP, because generated instances are deleted.
check() {
    local file=$1 mode flag dflag base message kept
    base=$(mktemp -d "$TMP/c.XXXXXX")
    for mode in early noearly; do
        flag= dflag=
        [ "$mode" = early ] || { flag=-no-early-tseitin; dflag=--no-early-tseitin; }
        message=
        run_baseline "$file" "$flag" "$base/proof" ||
            message="the baseline did not finish parsing in ${BASELINE_TIMEOUT}s"
        baseline_constraints "$base/proof" > "$base/expected"
        "$DUMP" $dflag "$file" 2> "$base/err" | grep '^o ' | LC_ALL=C sort > "$base/actual"
        if [ -z "$message" ] && ! cmp -s "$base/expected" "$base/actual"; then
            message="$(wc -l < "$base/expected") baseline constraints, $(wc -l < "$base/actual") new"
        fi
        if [ -n "$message" ]; then
            mkdir -p "$KEEP"
            kept=$KEEP/$(basename "$file")
            cp "$file" "$kept"
            printf '%s\n' "FAIL $file ($mode): $message" \
                "$(diff "$base/expected" "$base/actual" | head -5 | sed 's/^/  /')" \
                "$(head -3 "$base/err" | sed 's/^/  /')" \
                "  repro: $DUMP $dflag $kept | grep '^o ' | sort > new" \
                "         $BASELINE -verb=1 $flag -proof=P $kept   (interrupt after 'Parse time'), keep the o lines" \
                >> "$TMP/failures"
        fi
        [ -n "$message" ] || wc -l < "$base/actual" >> "$TMP/compared"
        rm -f "$base/proof"
    done
    rm -rf "$base"
}
export -f check baseline_constraints run_baseline
KEEP=/home/ec2-user/miniqu-work/encdiff-failed
export BASELINE DUMP BASELINE_TIMEOUT TMP KEEP

files=("$HERE"/regressions/*.qcir "$@")
for seed in $(seq "$FIRST" "$LAST"); do
    for tier in tiny search; do
        python3 "$HERE/corpus.py" --tier $tier --seed "$seed" --out "$TMP/$tier-$seed.qcir" 2> /dev/null ||
            { echo "FAIL corpus.py --tier $tier --seed $seed"; exit 1; }
        files+=("$TMP/$tier-$seed.qcir")
    done
done

touch "$TMP/failures" "$TMP/compared"
printf '%s\n' "${files[@]}" | taskset -c "0-$(($(nproc --all) / 2 - 1))" xargs -P "$JOBS" -I{} bash -c 'check "$1"' _ {}
cat "$TMP/failures"
failures=$(grep -c '^FAIL' "$TMP/failures")
echo "${#files[@]} instances, $(awk '{n += $1} END {print n + 0}' "$TMP/compared") constraints compared, $failures differences"
[ "$failures" -eq 0 ]
