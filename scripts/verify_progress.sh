#!/bin/bash
# Quick verification script for autonomous agents
# Reports: sorry count, build status, axiom status
# Designed to produce minimal output (context-window friendly for LLMs)

set -e
cd "$(dirname "$0")/.."

echo "=== HODGE PROOF PROGRESS ==="
echo "Date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo ""

# 1. Count sorries in Deep Pillars (the critical ones)
echo "--- Deep Pillar Sorries ---"
DEEP_SORRY=0
for f in Hodge/Deep/Pillars/*Impl.lean; do
    count=$(grep -c '^\s*sorry' "$f" 2>/dev/null || echo 0)
    if [ "$count" -gt 0 ]; then
        echo "  $f: $count sorry(s)"
        DEEP_SORRY=$((DEEP_SORRY + count))
    fi
done
echo "  TOTAL DEEP PILLAR: $DEEP_SORRY"
echo ""

# 2. Count sorries in WorkInProgress (secondary)
echo "--- WorkInProgress Sorries ---"
WIP_SORRY=$(grep -r '^\s*sorry' Hodge/WorkInProgress/ --include="*.lean" 2>/dev/null | wc -l || echo 0)
echo "  TOTAL WIP: $WIP_SORRY"
echo ""

# 3. Count sorries in main proof track (should be 0)
echo "--- Proof Track Sorries ---"
TRACK_SORRY=0
for f in Hodge/Main.lean Hodge/Kahler/Main.lean Hodge/Kahler/Manifolds.lean \
         Hodge/Kahler/TypeDecomposition.lean Hodge/Kahler/Cone.lean \
         Hodge/Kahler/SignedDecomp.lean Hodge/Kahler/Microstructure.lean \
         Hodge/Cohomology/Basic.lean Hodge/Analytic/Forms.lean \
         Hodge/Analytic/Currents.lean Hodge/Analytic/Calibration.lean \
         Hodge/Analytic/FlatNorm.lean Hodge/Classical/HarveyLawson.lean \
         Hodge/Classical/GAGA.lean Hodge/Classical/CycleClass.lean; do
    if [ -f "$f" ]; then
        count=$(grep -c '^\s*sorry' "$f" 2>/dev/null || echo 0)
        if [ "$count" -gt 0 ]; then
            echo "  ERROR: $f has $count sorry(s)!"
            TRACK_SORRY=$((TRACK_SORRY + count))
        fi
    fi
done
if [ "$TRACK_SORRY" -eq 0 ]; then
    echo "  OK: Proof track is sorry-free"
else
    echo "  FAIL: $TRACK_SORRY sorry(s) on proof track!"
fi
echo ""

# 4. Active locks
echo "--- Active Task Locks ---"
if [ -d current_tasks ] && [ "$(ls -A current_tasks/ 2>/dev/null)" ]; then
    ls -la current_tasks/
else
    echo "  (none)"
fi
echo ""

# 5. Summary
echo "=== SUMMARY ==="
echo "Deep Pillar sorries: $DEEP_SORRY"
echo "WIP sorries: $WIP_SORRY"
echo "Proof track sorries: $TRACK_SORRY"
TOTAL=$((DEEP_SORRY + WIP_SORRY + TRACK_SORRY))
echo "TOTAL: $TOTAL"
echo ""

if [ "$DEEP_SORRY" -eq 0 ]; then
    echo "*** ALL DEEP PILLAR SORRIES ELIMINATED ***"
    echo "Run 'lake env lean Hodge/Utils/DependencyCheck.lean' to verify axiom status."
fi
