#!/bin/bash
# Run Koka with profiling enabled
KOKA_BIN="/Users/timwhiting/koka/.stack-work/install/aarch64-osx/a9ec47c7352e958432b1b2d123bc85644ca90218f114dc7b116c6e281c6e8ee3/9.6.6/bin/koka"

echo "Starting profiled run at $(date)"
$KOKA_BIN analysis/test/build4.kk --dmcfar --sensitivity="(2,2)" +RTS -p -P -s -RTS

echo "Profiling completed at $(date)"
echo "Results:"
echo "  - koka.prof: Time and allocation profile"
echo "  - koka.hp: Heap profile (convert with: hp2ps -c koka.hp)"
echo ""
echo "Top functions by time:"
head -50 koka.prof | tail -30
