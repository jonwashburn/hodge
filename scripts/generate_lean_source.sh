#!/bin/bash
# Generate complete Lean source file for Hodge conjecture proof
# This script concatenates all Lean files with metadata for AI analysis

set -e

OUTPUT_FILE="LEAN_PROOF_BUNDLE.txt"
PROJECT_DIR="$(cd "$(dirname "$0")/.." && pwd)"

cd "$PROJECT_DIR"

echo "Generating $OUTPUT_FILE..."

{
    echo "================================================================================"
    echo "HODGE CONJECTURE - COMPLETE LEAN PROOF BUNDLE"
    echo "Generated: $(date)"
    echo "Project: $PROJECT_DIR"
    echo "================================================================================"
    echo ""
    
    # Count sorries and axioms
    echo "=== PROOF STATUS ==="
    echo ""
    echo "SORRIES:"
    grep -rn "sorry" Hodge/ --include="*.lean" 2>/dev/null | grep -v "This sorry" | grep -v "\-\- sorry" || echo "  (none)"
    echo ""
    
    echo "AXIOMS:"
    grep -rn "^axiom " Hodge/ --include="*.lean" 2>/dev/null || echo "  (none)"
    echo ""
    
    echo "OPAQUES:"
    grep -rn "^opaque " Hodge/ --include="*.lean" 2>/dev/null || echo "  (none)"
    echo ""
    
    # Summary counts
    SORRY_COUNT=$(grep -rn "sorry" Hodge/ --include="*.lean" 2>/dev/null | grep -v "This sorry" | grep -v "\-\- sorry" | wc -l | tr -d ' ')
    AXIOM_COUNT=$(grep -rn "^axiom " Hodge/ --include="*.lean" 2>/dev/null | wc -l | tr -d ' ')
    
    echo "=== SUMMARY ==="
    echo "Total sorries: $SORRY_COUNT"
    echo "Total axioms: $AXIOM_COUNT"
    echo ""
    
    echo "================================================================================"
    echo ""
    
    # Main proof files in dependency order
    echo "=== PROOF STRUCTURE (Dependency Order) ==="
    echo ""
    echo "Track A: Cohomology Foundation"
    echo "  - Hodge/Cohomology/Basic.lean"
    echo ""
    echo "Track B: Analytic/GMT Core"
    echo "  - Hodge/Analytic/Forms.lean"
    echo "  - Hodge/Analytic/Norms.lean"
    echo "  - Hodge/Analytic/Currents.lean"
    echo "  - Hodge/Analytic/IntegralCurrents.lean"
    echo "  - Hodge/Analytic/FlatNorm.lean"
    echo "  - Hodge/Analytic/Calibration.lean"
    echo ""
    echo "Track C: Kähler Geometry"
    echo "  - Hodge/Kahler/Manifolds.lean"
    echo "  - Hodge/Kahler/TypeDecomposition.lean"
    echo "  - Hodge/Kahler/Cone.lean"
    echo "  - Hodge/Kahler/SignedDecomp.lean"
    echo "  - Hodge/Kahler/Microstructure.lean"
    echo "  - Hodge/Kahler/Main.lean"
    echo ""
    echo "Track D: Classical Pillars"
    echo "  - Hodge/Classical/HarveyLawson.lean"
    echo "  - Hodge/Classical/Lefschetz.lean"
    echo "  - Hodge/Classical/FedererFleming.lean"
    echo "  - Hodge/Classical/GAGA.lean"
    echo ""
    echo "================================================================================"
    echo ""
    
    # Core proof files
    CORE_FILES=(
        "Hodge/Cohomology/Basic.lean"
        "Hodge/Analytic/Forms.lean"
        "Hodge/Analytic/Norms.lean"
        "Hodge/Analytic/Currents.lean"
        "Hodge/Analytic/IntegralCurrents.lean"
        "Hodge/Analytic/FlatNorm.lean"
        "Hodge/Analytic/Calibration.lean"
        "Hodge/Kahler/Manifolds.lean"
        "Hodge/Kahler/TypeDecomposition.lean"
        "Hodge/Kahler/Cone.lean"
        "Hodge/Kahler/SignedDecomp.lean"
        "Hodge/Kahler/Microstructure.lean"
        "Hodge/Kahler/Main.lean"
        "Hodge/Classical/HarveyLawson.lean"
        "Hodge/Classical/Lefschetz.lean"
        "Hodge/Classical/FedererFleming.lean"
        "Hodge/Classical/GAGA.lean"
        "Hodge/Main.lean"
    )
    
    # Additional infrastructure files
    INFRA_FILES=(
        "Hodge/Analytic/DomCoprod.lean"
        "Hodge/Analytic/ManifoldForms.lean"
        "Hodge/Analytic/Grassmannian.lean"
        "Hodge/Analytic/SheafTheory.lean"
        "Hodge/Classical/Bergman.lean"
        "Hodge/Classical/SerreVanishing.lean"
    )
    
    echo "=== CORE PROOF FILES ==="
    echo ""
    
    for file in "${CORE_FILES[@]}"; do
        if [ -f "$file" ]; then
            LINE_COUNT=$(wc -l < "$file" | tr -d ' ')
            echo "================================================================================"
            echo "FILE: $file ($LINE_COUNT lines)"
            echo "================================================================================"
            cat "$file"
            echo ""
        fi
    done
    
    echo ""
    echo "=== INFRASTRUCTURE FILES ==="
    echo ""
    
    for file in "${INFRA_FILES[@]}"; do
        if [ -f "$file" ]; then
            LINE_COUNT=$(wc -l < "$file" | tr -d ' ')
            echo "================================================================================"
            echo "FILE: $file ($LINE_COUNT lines)"
            echo "================================================================================"
            cat "$file"
            echo ""
        fi
    done
    
    # Any remaining Lean files
    echo ""
    echo "=== OTHER LEAN FILES ==="
    echo ""
    
    find Hodge/ -name "*.lean" -type f 2>/dev/null | while read -r file; do
        # Skip files already included
        skip=false
        for core in "${CORE_FILES[@]}" "${INFRA_FILES[@]}"; do
            if [ "$file" = "$core" ]; then
                skip=true
                break
            fi
        done
        if [ "$skip" = false ]; then
            LINE_COUNT=$(wc -l < "$file" | tr -d ' ')
            echo "================================================================================"
            echo "FILE: $file ($LINE_COUNT lines)"
            echo "================================================================================"
            cat "$file"
            echo ""
        fi
    done
    
    # Mathlib overlays
    echo ""
    echo "=== MATHLIB OVERLAYS ==="
    echo ""
    
    find Mathlib/ -name "*.lean" -type f 2>/dev/null | while read -r file; do
        LINE_COUNT=$(wc -l < "$file" | tr -d ' ')
        echo "================================================================================"
        echo "FILE: $file ($LINE_COUNT lines)"
        echo "================================================================================"
        cat "$file"
        echo ""
    done
    
    echo "================================================================================"
    echo "END OF PROOF BUNDLE"
    echo "================================================================================"
    
} > "$OUTPUT_FILE"

echo "Generated $OUTPUT_FILE"
echo ""
echo "Statistics:"
wc -l "$OUTPUT_FILE"
echo ""
echo "Sorry count: $SORRY_COUNT"
echo "Axiom count: $AXIOM_COUNT"

# Also create a timestamped session snapshot (requested workflow)
DATE_TAG="$(date +"%Y%m%d_%H%M%S")"
SESSION_FILE="SESSION_${DATE_TAG}_LEAN_PROOF.txt"
cp "$OUTPUT_FILE" "$SESSION_FILE"
echo ""
echo "Created session snapshot: $SESSION_FILE"

