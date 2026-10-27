#!/bin/zsh
# One benchmark job, run like run-benchmarks.kk does from the repository root, in its own directory:
#   job.sh <set> <binary-mode> <file> <flag> <d> <m>
# <set> is where the results go (runs/<set>/...), <binary-mode> picks koka-<binary-mode> (lose, add, keep).
S=${0:A:h}
set=$1 bin=$2 file=$3 flag=$4 d=$5 m=$6
B=$(cat $S/bindir)
dir=$S/runs/$set/${file//\//_}${flag}-$d-$m
mkdir -p $dir && cd $dir && rm -rf analysis && cp -R $S/analysis analysis   # a real copy: module names follow the path
start=$(date +%s)
$B/koka-$bin -l analysis/benchmarks/$file.kk $flag --sensitivity="($d,$m)" > log.txt 2>&1
code=$?
echo "$set $file $flag ($d,$m) exit=$code $(( $(date +%s) - start ))s" >> $S/progress.txt
