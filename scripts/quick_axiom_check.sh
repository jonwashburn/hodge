#!/bin/bash
# Quick axiom check - works even when build is broken
# Checks for explicit `axiom` declarations in the codebase
#
# This is a FAST check that doesn't require building. It catches:
# - New `axiom` declarations added to the codebase
# - Does NOT catch sorries (those require a build)
#
# For full verification, use: ./scripts/verify_proof_track.sh

set -e
cd "$(dirname "$0")/.."

echo "═══════════════════════════════════════════════════════"
echo "QUICK AXIOM CHECK (no build required)"
echo "═══════════════════════════════════════════════════════"
echo ""

# Find all axiom declarations (must start line with "axiom " - not in comments)
# Filter out:
# - Lines ending with -/ (inside docstrings)
# - Lines containing -- (inline comments)
# The pattern "^axiom [a-zA-Z]" catches real axiom declarations
AXIOMS=$(grep -rn "^axiom [a-zA-Z]" Hodge/ --include="*.lean" 2>/dev/null | grep -v "\-/$" | grep -v " -- " || true)

if [ -z "$AXIOMS" ]; then
    echo "✅ No explicit 'axiom' declarations found in Hodge/"
    echo ""
    echo "Note: This check is fast but incomplete. For full verification:"
    echo "  ./scripts/verify_proof_track.sh"
    exit 0
fi

echo "⚠️  Found axiom declaration(s) in Hodge/:"
echo ""
echo "$AXIOMS"
echo ""

# Check if any are in the proof track (i.e., imported by Hodge.Main)
echo "═══════════════════════════════════════════════════════"
echo "CHECKING IF AXIOMS ARE ON PROOF TRACK"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "Files with axioms:"
echo "$AXIOMS" | cut -d: -f1 | sort -u

echo ""
echo "Run './scripts/verify_proof_track.sh' for full verification."
echo "(Requires successful build)"
