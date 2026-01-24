# N4: Prove Laplacian Self-Adjointness and Nonnegativity

**Re-queue this prompt until the checkbox is checked.**

> **Prerequisites**: N3 (d-δ adjointness).
> This is a NICE-TO-HAVE item for the analytic Hodge library.

## Cursor Notes

```
# Hodge Conjecture Lean 4 Formalization

## CRITICAL: Mathlib Cache (NEVER rebuild Mathlib from source!)
Before running ANY `lake build` command, ALWAYS run:
  lake exe cache get

## Build Commands
  ./scripts/build.sh           # Safe build with cache
  lake env lean <file.lean>    # Check single file
  lake build Hodge             # Build all

## Verification Commands
  lake env lean Hodge/Utils/DependencyCheck.lean  # Check axioms

## Key Files for This Task
  - archive/Hodge/Analytic/Laplacian/HodgeLaplacian.lean  # Δ definition
  - archive/Hodge/Analytic/HodgeLaplacian.lean            # Top-level API
```

## Current State

We have (in archive):
- `laplacian_construct ω = castForm _ (d(δω)) + castForm _ (δ(dω))` — the Hodge Laplacian
- Placeholder theorems: `hodgeLaplacian_selfAdjoint := trivial`, `hodgeLaplacian_nonneg := trivial`

## What It Should Be

### Self-Adjointness
```lean
theorem hodgeLaplacian_selfAdjoint (ω η : SmoothForm n X k) :
    L2Inner_measure μ (Δ ω) η = L2Inner_measure μ ω (Δ η)
```

### Nonnegativity
```lean
theorem hodgeLaplacian_nonneg (ω : SmoothForm n X k) :
    0 ≤ L2Inner_measure μ ω (Δ ω)
```

Or equivalently: `⟪Δω, ω⟫ = ‖dω‖² + ‖δω‖² ≥ 0`

## Proof Strategy

### Self-Adjointness
Using N3 (d-δ adjointness):
```
⟪Δω, η⟫ = ⟪dδω + δdω, η⟫
        = ⟪dδω, η⟫ + ⟪δdω, η⟫
        = ⟪δω, δη⟫ + ⟪dω, dη⟫   (by adjointness)
        = ⟪ω, dδη⟫ + ⟪ω, δdη⟫   (by adjointness again)
        = ⟪ω, Δη⟫
```

### Nonnegativity
```
⟪Δω, ω⟫ = ⟪dδω + δdω, ω⟫
        = ⟪δω, δω⟫ + ⟪dω, dω⟫
        = ‖δω‖² + ‖dω‖²
        ≥ 0
```

## Definition of Done

- [ ] `hodgeLaplacian_selfAdjoint` is proved (not `trivial`)
- [ ] `hodgeLaplacian_nonneg` is proved (not `trivial`)
- [ ] `lake build Hodge` succeeds
- [ ] No new axioms introduced

## Progress Log

(Add entries as you work)

- [ ] Started investigation
- [ ] Verified N3 (adjointness) is available
- [ ] Proved self-adjointness
- [ ] Proved nonnegativity
- [ ] Verified build passes

---
**When this is complete, check off D.2 in `docs/REQUEUE_ANALYTIC_HODGE_STACK.md`**
