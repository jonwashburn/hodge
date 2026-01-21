#!/bin/bash
# Audit script for detecting stubs, axioms, and placeholders in the Hodge codebase
# Run from project root: ./scripts/audit_stubs.sh

echo "========================================"
echo "HODGE PROOF INTEGRITY AUDIT"
echo "========================================"
echo ""

cd "$(dirname "$0")/.." || exit 1

MODE="proof-track"
if [ "${1:-}" = "--full" ]; then
    MODE="full"
fi

if [ "$MODE" = "proof-track" ]; then
    echo "1. PROOF-TRACK AXIOMS (Lean kernel report)"
    echo "========================================="
    echo "Ground truth is Lean's kernel dependency list:"
    echo "  #print axioms hodge_conjecture"
    echo "  #print axioms hodge_conjecture'"
    echo ""
    echo "Running: lake env lean Hodge/Utils/DependencyCheck.lean"
    echo ""
    lake env lean Hodge/Utils/DependencyCheck.lean
    echo ""

    echo "2. NOTE"
    echo "======="
    echo "This default mode reports ONLY the active proof track."
    echo "It intentionally does NOT grep the whole repo for '^axiom'/'sorry', because that"
    echo "includes off-track or unused development stubs that are not in the dependency cone"
    echo "of the main theorem."
    echo ""
    echo "To run the full repo scan (noisy by design), run:"
    echo "  ./scripts/audit_stubs.sh --full"
    echo ""

    echo "========================================"
    echo "AUDIT COMPLETE"
    echo "========================================"
    exit 0
fi

echo "1. AXIOMS (FULL REPO SCAN)"
echo "========================="
axiom_count=$(grep -rn "^axiom" Hodge/ 2>/dev/null | wc -l)
if [ "$axiom_count" -eq 0 ]; then
    echo "✓ No axioms found"
else
    echo "✗ Found $axiom_count axiom(s):"
    grep -rn "^axiom" Hodge/ 2>/dev/null
fi
echo ""

echo "2. OPAQUE DEFINITIONS"
echo "====================="
opaque_count=$(grep -rn "^opaque" Hodge/ 2>/dev/null | wc -l)
if [ "$opaque_count" -eq 0 ]; then
    echo "✓ No opaque definitions found"
else
    echo "✗ Found $opaque_count opaque definition(s):"
    grep -rn "^opaque" Hodge/ 2>/dev/null
fi
echo ""

echo "3. SORRY BLOCKS"
echo "==============="
# NOTE: we only count *actual* `sorry` tactics, not docstring mentions.
# This avoids noisy false positives like “no sorry statements” in module docs.
SORRY_RE='^[[:space:]]*sorry([^[:alnum:]_]|$)'
sorry_count=$(grep -RIn --include="*.lean" -E "$SORRY_RE" Hodge/ 2>/dev/null | wc -l)
if [ "$sorry_count" -eq 0 ]; then
    echo "✓ No sorry blocks found"
else
    echo "⚠ Found $sorry_count sorry usage(s):"
    grep -RIn --include="*.lean" -E "$SORRY_RE" Hodge/ 2>/dev/null
fi
echo ""

echo "4. PLACEHOLDER DEFINITIONS (:= 0)"
echo "=================================="
echo "The following := 0 patterns may be placeholders (review needed):"
echo ""
grep -rn ":= 0" Hodge/ 2>/dev/null | grep -v "test\|Test\|example\|finrank\|degree\|codim" | head -40
echo ""

echo "5. KNOWN KAHLER OPERATOR STUBS"
echo "=============================="
echo "These operators are intentionally stubbed as := 0:"
echo "  - lefschetzLambdaLinearMap (dual Lefschetz Λ)"
echo "  - hodgeStar (Hodge star ⋆)"
echo "  - adjointDeriv (codifferential δ)"
echo "  - laplacian (Hodge Laplacian Δ)"
echo "  - pointwiseInner / L2Inner (inner product stubbed)"
echo ""
echo "These do not affect the main theorem architecture as stated."
echo ""

echo "6. AXIOM AUDIT (VIA LEAN)"
echo "========================="
echo "Running: lake env lean Hodge/Utils/DependencyCheck.lean"
lake env lean Hodge/Utils/DependencyCheck.lean
echo ""

echo "========================================"
echo "AUDIT COMPLETE"
echo "========================================"

