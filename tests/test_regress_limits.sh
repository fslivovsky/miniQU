#!/bin/bash
# Self-test of the per-row timeout limit of tests/regress.sh (ROADMAP 0.1): a
# fake solver that hangs on about 30% of the instances passes a stress row with
# limit 50 and fails it with limit 2; a malformed or misplaced limit is an
# error naming file and line.
#
# Usage: tests/test_regress_limits.sh
HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${REGRESS_WORK:-/home/ec2-user/miniqu-work/regress}/limits
mkdir -p "$WORK"
fake=$HERE/fake/hang-30.sh
status=0

# run NAME ROW EXPECTED_EXIT PATTERN: one matrix with the single row ROW.
run() {
    local name=$1 row=$2 want=$3 pattern=$4
    echo "$row" > "$WORK/$name.txt"
    REGRESS_WORK=$WORK/$name "$HERE/regress.sh" -S -n -s 1:60 -j 8 -t 2 -m "$WORK/$name.txt" "$fake" \
        > "$WORK/$name.log" 2>&1
    local got=$?
    if [ $got -ne "$want" ] || ! grep -q -- "$pattern" "$WORK/$name.log"; then
        echo "FAIL $name: exit $got (want $want), pattern '$pattern' (log $WORK/$name.log)"
        status=1
    else
        echo "ok   $name"
    fi
}

run limit-50 'fake | | no | conflicts | stress | 50' 0 'limit 50%'
run limit-2 'fake | | no | conflicts | stress | 2' 1 'FAIL \[fake\] stress configuration: .* (limit 2%)'
run default-limit 'fake | | no | conflicts | stress' 1 '(limit 2%)'
run limit-on-normal-row 'fake | | no | conflicts | normal | 5' 1 'limit-on-normal-row.txt:1: the limit "5"'
run malformed-limit 'fake | | no | conflicts | stress | many' 1 'malformed-limit.txt:1: the limit "many"'
exit $status
