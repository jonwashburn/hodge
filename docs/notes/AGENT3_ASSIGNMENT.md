# Agent 3 Assignment: Complete HasBoundaryBound API Propagation

**Date**: January 11, 2026  
**Priority**: HIGH - Blocking full build

---

## Context

The `smoothExtDeriv_comass_bound` axiom has been **successfully removed** from `Hodge/Analytic/Currents.lean` by switching from a global axiom to an explicit `HasBoundaryBound` predicate approach.

**Key insight**: The claim "d is bounded in C^0 norm" was FALSE. Instead, we now require:
- Explicit proof that a current has a boundary bound (trivial for zero current)
- Closure under add, neg, smul, sub operations
- `Current.boundary` takes an explicit `HasBoundaryBound` proof

This is a **genuine improvement** that removes a false axiom from the proof track.

---

## Current Build Status

The build fails in:
- `Hodge/Analytic/FlatNorm.lean` - Many type mismatches and proof failures
- Downstream files that use `Current.boundary`

---

## Your Task

### 1. Fix `Hodge/Analytic/FlatNorm.lean`

The new API for `Current.boundary` is:
```lean
def boundary (T : Current n X (k + 1)) (h : HasBoundaryBound T) : Current n X k
```

Key changes needed:
1. **`flatNormDecompSet`** now includes `hR : Current.HasBoundaryBound R` in the existential
2. All destructuring patterns like `⟨S, R, hT, hm⟩` must become `⟨S, R, hR, hT, hm⟩`
3. Calls to `Current.boundary R` must become `Current.boundary R hR`
4. The `flatNorm_boundary_le` theorem needs `hS : HasBoundaryBound S` for decomposition elements

**Strategy**: For the FlatNorm theorems:
- When S appears in a decomposition, we generally need `HasBoundaryBound S` 
- Option A: Add `hS : HasBoundaryBound S` to `flatNormDecompSet`
- Option B: Work with specific cases where S = 0 (trivially bounded) or S = c • T for known T

The cleanest approach is Option A: extend `flatNormDecompSet` to require bounds on both S and R.

### 2. Fix `Hodge/Analytic/IntegralCurrents.lean`

Similar updates needed:
- `polyhedral_boundary` uses the old API
- `isIntegral_boundary` uses the old API

### 3. Fix Downstream Files

- `Hodge/Kahler/Microstructure.lean`
- `Hodge/Classical/HarveyLawson.lean`
- `Hodge/Classical/FedererFleming.lean`

---

## Key Helper Theorems Already Available

In `Currents.lean`:
```lean
theorem zero_hasBoundaryBound : HasBoundaryBound (0 : Current n X (k + 1))
theorem add_hasBoundaryBound : HasBoundaryBound S → HasBoundaryBound T → HasBoundaryBound (S + T)
theorem neg_hasBoundaryBound : HasBoundaryBound T → HasBoundaryBound (-T)
theorem smul_hasBoundaryBound : HasBoundaryBound T → HasBoundaryBound (c • T)
theorem sub_hasBoundaryBound : HasBoundaryBound S → HasBoundaryBound T → HasBoundaryBound (S - T)
theorem boundary_hasBoundaryBound : HasBoundaryBound T → HasBoundaryBound (boundary T h)
```

---

## Success Criterion

```bash
lake build Hodge.Analytic.Currents
# Must succeed

lake build Hodge.Analytic.FlatNorm
# Must succeed

lake build Hodge.Analytic.IntegralCurrents
# Must succeed

lake build
# Full build must succeed
```

After completion, run:
```bash
cat > /tmp/check.lean << 'EOF'
import Hodge.Analytic.Currents
#print axioms Current.boundary
EOF
lake env lean /tmp/check.lean
```

The output should show NO `smoothExtDeriv_comass_bound` axiom.

---

## What NOT To Do

- ❌ Do NOT revert the HasBoundaryBound changes
- ❌ Do NOT introduce a new axiom to replace the removed one
- ❌ Do NOT add `sorry` to make things compile

---

## Estimated Effort

- FlatNorm.lean: ~30 minutes of careful updates
- IntegralCurrents.lean: ~15 minutes
- Downstream files: ~15 minutes each

Total: ~2 hours of focused work

---

## Files to Modify (in order)

1. `/Users/jonathanwashburn/Projects/hodge/Hodge/Analytic/FlatNorm.lean`
2. `/Users/jonathanwashburn/Projects/hodge/Hodge/Analytic/IntegralCurrents.lean`
3. `/Users/jonathanwashburn/Projects/hodge/Hodge/Kahler/Microstructure.lean`
4. `/Users/jonathanwashburn/Projects/hodge/Hodge/Classical/HarveyLawson.lean`
5. `/Users/jonathanwashburn/Projects/hodge/Hodge/Classical/FedererFleming.lean`
