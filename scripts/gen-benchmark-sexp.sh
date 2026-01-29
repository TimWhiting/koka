#!/bin/bash
# Generate S-expression core files for all benchmarks

set -e

KOKA="stack exec koka --"
OUTPUT_DIR="benchmark-sexp"

# Create output directory
mkdir -p "$OUTPUT_DIR"

# Suite benchmarks (have main, compile normally)
echo "Compiling suite benchmarks..."
$KOKA --core \
  analysis/benchmarks/suite/basic.kk \
  analysis/benchmarks/suite/nondet.kk \
  analysis/benchmarks/suite/nested.kk \
  analysis/benchmarks/suite/multi-effect.kk \
  analysis/benchmarks/suite/recursion.kk \
  analysis/benchmarks/suite/state-handler.kk \
  analysis/benchmarks/suite/complex-flow.kk \
  analysis/benchmarks/suite/nested-nondet.kk

# Handler benchmarks (no main, compile as library)
echo "Compiling handler benchmarks..."
for f in yield vec unix nim ambient scoped; do
  $KOKA --core -l analysis/benchmarks/handlers/$f.kk
done

# Rosetta benchmarks
echo "Compiling rosetta benchmarks..."
$KOKA --core -l analysis/benchmarks/rosetta/rosetta/0-nums/pr4rings.kk
$KOKA --core -l analysis/benchmarks/rosetta/rosetta/j/jump-anywhere.kk
$KOKA --core -l analysis/benchmarks/rosetta/rosetta/m/monads-writer.kk

# Koka-gen benchmarks
echo "Compiling koka-gen benchmarks..."
for f in build interp interp2 mini-ppl music scheduler ukanren coop-communication; do
  $KOKA --core -l analysis/benchmarks/koka-gen/$f.kk
done

# Copy all .kkcs files to output directory
echo "Copying .kkcs files to $OUTPUT_DIR..."
find .koka -name "*.kkcs" -exec cp {} "$OUTPUT_DIR/" \;

echo "Done! Generated $(ls -1 "$OUTPUT_DIR"/*.kkcs | wc -l) .kkcs files in $OUTPUT_DIR/"
