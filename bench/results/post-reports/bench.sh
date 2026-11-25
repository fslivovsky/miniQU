#!/bin/bash
# Performance, regression and ablation runs: 376 instances, 60 s, 24 jobs on cores 24-47, 8 GB.
cd ~/miniQU; O=~/miniqu-work/post; B=~/miniqu-work/build
NEW=$B/bench-post/miniQU; BASE=~/miniqu-work/baseline/miniQU; M1=$B/bench-M1-r3/miniQU
run() { # tag solver seed args [extra run.py options]
  tag=$1; sol=$2; seed=$3; args=$4; shift 4
  [ -f bench/results/$tag/results.csv ] && return
  echo "=== $tag start $(date -u +%H:%M)" >> $O/bench.summary
  python3 bench/run.py --solver $sol --tag $tag --timeout 60 --seed $seed --jobs 24 --cores 24-47 --mem-gb 8 --args="$args" "$@" > $O/$tag.log 2>&1
  echo "=== $tag rc=$? end $(date -u +%H:%M) $(tail -1 $O/$tag.log | cut -c1-150)" >> $O/bench.summary
}
main() { s=$1
  for d in "" "-dl"; do n=${d:+-dl}
    run post-ref$n-s$s    $NEW $s "$d"
    run post-elim$n-s$s   $NEW $s "--elim $d"
    run post-vivify$n-s$s $NEW $s "--vivify $d"
    run post-both$n-s$s   $NEW $s "--elim --vivify $d"
    run post-base$n-s$s   $BASE $s "$d" --seed-args '-rnd-init -rnd-seed={seed}'
  done
}
main 1
run post-m1-s1    $M1 1 ""
run post-m1-dl-s1 $M1 1 "-dl"
# one switch at a time, seed 1
run post-elim-clauseonly-s1   $NEW 1 "--elim --no-elimcube"
run post-elim-cubeonly-s1     $NEW 1 "--elim --no-elimclause"
run post-elim-preonly-s1      $NEW 1 "--elim --no-eliminp"
run post-elim-inponly-s1      $NEW 1 "--elim --no-elimpre"
run post-vivify-clauseonly-s1 $NEW 1 "--vivify --no-vivifycube"
run post-vivify-cubeonly-s1   $NEW 1 "--vivify --no-vivifyclause"
run post-vivify-tier3-s1      $NEW 1 "--vivify --vivifytier=3"
run post-notiers-s1           $NEW 1 "--no-tiers --no-glueupdate"
run post-norootsimp-s1        $NEW 1 "--no-rootsimp"
run post-noreusetrail-s1      $NEW 1 "--no-reusetrail"
# Lean proof coverage with both techniques on
run post-proofcov-both-s0    $NEW 0 "--elim --vivify"     --proof-check --proof-max-solve-sec 20 --proof-timeout 600 --proof-jobs 12 --proof-cores 24-47
run post-proofcov-both-dl-s0 $NEW 0 "--elim --vivify -dl" --proof-check --proof-max-solve-sec 20 --proof-timeout 600 --proof-jobs 12 --proof-cores 24-47
main 2
main 3
echo ALLDONE >> $O/bench.summary
