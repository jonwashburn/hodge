#!/bin/bash
# Verify that hodge_conjecture' only depends on expected axioms
# This script should be run before any merge to main

set -e

cd "$(dirname "$0")/.."

echo "📦 Fetching Mathlib cache..."
lake exe cache get 2>&1 | tail -1

echo ""
echo "🔍 Checking proof track axioms for hodge_conjecture'..."
echo ""

# Get the full output
OUTPUT=$(lake env lean Hodge/Utils/DependencyCheck.lean 2>&1)

# Extract the hodge_conjecture' block (everything after the second 'depends on')
AXIOM_BLOCK=$(echo "$OUTPUT" | awk "/^'hodge_conjecture''/{flag=1} flag" | head -7)

echo "$AXIOM_BLOCK"
echo ""

# Extract axiom names more carefully - get everything between [ and ], clean it up
AXIOM_LIST=$(echo "$AXIOM_BLOCK" | \
    sed 's/.*\[//' | \
    sed 's/\].*//' | \
    tr ',' '\n' | \
    tr -d ' ' | \
    grep -v "^$")

echo "═══════════════════════════════════════════════════════"
echo "AXIOM ANALYSIS"
echo "═══════════════════════════════════════════════════════"

CUSTOM_COUNT=0
SORRY_FOUND=0

for axiom in $AXIOM_LIST; do
    case "$axiom" in
        propext)
            echo "  ✅ propext (standard Lean - proposition extensionality)"
            ;;
        Classical.choice)
            echo "  ✅ Classical.choice (standard Lean - axiom of choice)"
            ;;
        Quot.sound)
            echo "  ✅ Quot.sound (standard Lean - quotient soundness)"
            ;;
        sorryAx)
            echo "  ❌ sorryAx (SORRY STATEMENTS IN CODE!)"
            SORRY_FOUND=1
            ;;
        "")
            ;;
        *)
            echo "  🔴 $axiom (CUSTOM AXIOM - must prove)"
            CUSTOM_COUNT=$((CUSTOM_COUNT + 1))
            ;;
    esac
done

echo ""
echo "═══════════════════════════════════════════════════════"
echo "SUMMARY"
echo "═══════════════════════════════════════════════════════"
echo "   Standard Lean axioms: 3 (always present, acceptable)"
echo "   Custom axioms to prove: $CUSTOM_COUNT"

if [ $SORRY_FOUND -eq 1 ]; then
    echo "   Sorry statements: FOUND ❌"
    echo ""
    echo "❌ CRITICAL: Remove sorry statements first!"
    echo "   Find them: grep -rn 'sorry' Hodge/ --include='*.lean'"
    exit 1
fi

if [ $CUSTOM_COUNT -eq 0 ]; then
    echo ""
    echo "✅ SUCCESS: Proof is complete! No custom axioms or sorry."
    exit 0
else
    echo ""
    echo "⚠️  Proof incomplete: $CUSTOM_COUNT custom axiom(s) remain."
    echo ""
    echo "Custom axioms to eliminate:"
    for axiom in $AXIOM_LIST; do
        case "$axiom" in
            propext|Classical.choice|Quot.sound|sorryAx|"")
                ;;
            *)
                # Find location
                LOC=$(grep -rn "^axiom $axiom" Hodge/ --include="*.lean" 2>/dev/null | head -1 | cut -d: -f1-2)
                if [ -z "$LOC" ]; then
                    # Try without ^ anchor
                    LOC=$(grep -rn "axiom $axiom" Hodge/ --include="*.lean" 2>/dev/null | head -1 | cut -d: -f1-2)
                fi
                echo "   - $axiom ($LOC)"
                ;;
        esac
    done
    exit 0
fi
