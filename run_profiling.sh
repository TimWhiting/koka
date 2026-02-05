#!/bin/bash
# Run Koka with profiling enabled
KOKA_BIN=".stack-work/install/aarch64-osx/a9ec47c7352e958432b1b2d123bc85644ca90218f114dc7b116c6e281c6e8ee3/9.6.6/bin/koka"

echo "Starting profiled run at $(date)"
$KOKA_BIN analysis/test/interp2-t3.kk --dmcfa --sensitivity="(0,0)" +RTS -p -P -s -RTS

echo "Profiling completed at $(date)"
echo "Results:"
echo "  - koka.prof: Time and allocation profile"
echo "  - koka.hp: Heap profile (convert with: hp2ps -c koka.hp)"
echo ""
echo "Top functions by time:"
head -50 koka.prof | tail -30
