#!/bin/bash
# Fidelity of M1-T11: conflict counts of one binary on search seeds 151..300
# (instances of /home/ec2-user/miniqu-work/stress-t08/inst), seed 0, 60 s,
# in four configurations.  The baseline takes the same option names.
#   run.sh LABEL BINARY OUT.csv   ->  label,seed,config,exit,conflicts
# (conflicts empty on timeout).  Lower half of the cores, 16 jobs: counts
# only, no timing.
I=/home/ec2-user/miniqu-work/stress-t08/inst
export I LABEL=$1 BIN=$2
one() {
  s=$1
  for opt in default -dl -mode=1 -mode=2; do
    o=$opt; [ $o = default ] && o=
    out=$(timeout 60 $BIN -verb=1 $o $I/s$s.qcir 2>&1); ec=$?
    c=$(echo "$out" | awk '($1=="c" && $2=="stat" && $3=="conflicts") {print $4} /^conflicts /{print $3}' | head -1)
    [ $ec = 124 ] && c=
    echo "$LABEL,$s,$opt,$ec,$c"
  done
}
export -f one
seq 151 300 | taskset -c 0-47 xargs -P 16 -I{} bash -c 'one {}' | sort -t, -k2,2n -k3,3 > $3
