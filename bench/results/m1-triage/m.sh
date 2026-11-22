#!/bin/bash
# usage: m.sh NAME OPTS...  -> NAME.csv: seed,exit,time,conflicts,restarts,dependencies,depresets,reductions,collections,relocated
D=/home/ec2-user/miniqu-work/triage; I=/home/ec2-user/miniqu-work/stress-t08/inst
name=$1; shift
export D I bin=${BIN:-/home/ec2-user/miniqu-work/build/release/miniQU} TO=${TO:-20} OPTS="$*"
one() {
  s=$1; f=$I/s$s.qcir
  st=$(date +%s.%N)
  out=$(timeout $TO $bin -verb=1 $OPTS $f 2>&1); ec=$?
  en=$(date +%s.%N)
  g() { echo "$out" | awk -v k=$1 '$1=="c" && $2=="stat" && $3==k {print $4}' | head -1; }
  echo "$s,$ec,$(echo "$en - $st" | bc),$(g conflicts),$(g restarts),$(g dependencies),$(g depresets),$(g reductions),$(g collections),$(g relocated)"
}
export -f one
seq 151 300 | taskset -c 16-47 xargs -P 16 -I{} bash -c 'one {}' | sort -n > $D/$name.csv
