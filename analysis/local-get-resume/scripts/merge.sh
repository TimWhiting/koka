#!/bin/zsh
# Merge job results into merged/<mode>/benchmarks/results: the shared runs plus that mode's runs.
S=${0:A:h}
rm -rf $S/merged
for mode in lose add keep; do
  out=$S/merged/$mode/benchmarks/results
  mkdir -p $out
  for d in $S/runs/shared/*/benchmarks/results(N) $S/runs/$mode/*/benchmarks/results(N); do
    rsync -a $d/ $out/
  done
done
find $S/merged -name "*.json" | awk -F/ '{print $(NF-0)}' | wc -l
