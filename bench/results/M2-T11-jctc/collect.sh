#!/bin/bash
# usage: collect.sh RESDIR > runs.csv
# RESDIR holds one line per run (arm,config,instance,seed,exit,wall,conflicts) written by the M2-T11 job script.
# Instance names may contain a comma (jctc16-vals-0,2-pass), so the instance is rebuilt from the fields between
# config and the last four fields, and quoted. Conflicts are kept only for solved runs of the M2 arms (3-11).
echo "arm,config,instance,seed,exit,wall,conflicts"
for f in "$1"/*; do case $f in *.tmp) continue;; esac; cat "$f"; done |
  awk -F, '{ inst=$3; for (i=4; i<=NF-4; i++) inst=inst "," $i
             seed=$(NF-3); rc=$(NF-2); wall=$(NF-1); conf=$NF
             if (!($1>=3 && (rc==10 || rc==20))) conf=""
             printf "%s,%s,\"%s\",%s,%s,%s,%s\n", $1, $2, inst, seed, rc, wall, conf }' |
  sort -t, -k2,2r -k3,3 -k4,4n -k1,1n
