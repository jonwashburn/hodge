#!/bin/bash
# verify_agent_work.sh
# Verifies that agent changes are actual proofs, not trivializations

set -e

echo "=== Deep Track Agent Work Verification ==="
echo ""

cd "$(dirname "$0")/../.."

# Check 1: No trivializations
echo "Checking for trivializations..."
TRIVIALS=$(grep -rn ":= trivial\|:= True\|:= ⟨⟩\|:= by simp\s*$\|:= by rfl\s*$\|:= by exact trivial" Hodge/Deep/Pillars/*.lean 2>/dev/null | grep -v "placeholder\|Status" || true)

if [ -n "$TRIVIALS" ]; then
    echo "❌ FAIL: Found trivializations:"
    echo "$TRIVIALS"
    echo ""
    echo "Agents must NOT trivialize goals. Use sorry if blocked."
    exit 1
fi
echo "✓ No trivializations found"
echo ""

# Check 2: No admit
echo "Checking for admit..."
ADMITS=$(grep -rn "\badmit\b" Hodge/Deep/Pillars/*.lean 2>/dev/null || true)

if [ -n "$ADMITS" ]; then
    echo "❌ FAIL: Found admit:"
    echo "$ADMITS"
    exit 1
fi
echo "✓ No admit found"
echo ""

# Check 3: Count sorries
echo "Counting remaining sorries..."
SORRY_COUNT=$(grep -r "sorry" Hodge/Deep/Pillars/*.lean 2>/dev/null | grep -v "Status\|NEEDS\|would" | wc -l | tr -d ' ')
echo "Current sorry count: $SORRY_COUNT"
echo ""

# Check 4: Build succeeds
echo "Building deep track..."
lake exe cache get > /dev/null 2>&1
if lake build Hodge.Deep 2>&1 | grep -q "error:"; then
    echo "❌ FAIL: Build errors in deep track"
    lake build Hodge.Deep 2>&1 | grep "error:"
    exit 1
fi
echo "✓ Build successful"
echo ""

# Check 5: Proof track still clean
echo "Verifying proof track..."
AXIOMS=$(lake env lean Hodge/Utils/DependencyCheck.lean 2>&1 | grep "depends on axioms")
if echo "$AXIOMS" | grep -q "sorryAx"; then
    echo "❌ FAIL: Proof track has sorryAx"
    echo "$AXIOMS"
    exit 1
fi
echo "✓ Proof track still kernel-clean"
echo ""

echo "=== Verification Complete ==="
echo "Sorry count: $SORRY_COUNT"
echo ""
echo "If sorry count decreased, agent made progress!"
echo "If sorry count stayed same but no errors, agent didn't trivialize."
