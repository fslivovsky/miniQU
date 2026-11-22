#!/bin/bash
# T10's -no-early-tseitin comparison, redone for M1-T11: search seeds
# 1001..1200 (instances in /home/ec2-user/miniqu-work/noearly), seed 0,
# 20 s, both binaries, upper half of the cores, 24 seeds at a time (48
# processes at most).  Output: seed,exit_new,time_new,exit_baseline,time_baseline
D=/home/ec2-user/miniqu-work/noearly
export D R=${R:-/home/ec2-user/miniqu-work/build/release/miniQU} B=/home/ec2-user/miniqu-work/baseline/miniQU
one() {
  s=$1
  t0=$(date +%s.%N); timeout 20 $R -no-earlytseitin $D/s$s.qcir >/dev/null 2>&1; a=$?; t1=$(date +%s.%N)
  timeout 20 $B -no-early-tseitin $D/s$s.qcir >/dev/null 2>&1; b=$?; t2=$(date +%s.%N)
  echo "$s,$a,$(echo "$t1 - $t0" | bc),$b,$(echo "$t2 - $t1" | bc)"
}
export -f one
seq 1001 1200 | taskset -c 48-95 xargs -P 24 -I{} bash -c 'one {}' | sort -n
