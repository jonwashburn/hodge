# N5: Prove Kernel Characterization (Δω = 0 ↔ dω = 0 ∧ δω = 0)

**Re-queue this prompt until the checkbox is checked.**

> **Prerequisites**: N4 (Laplacian nonnegativity).
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
  - archive/Hodge/Analytic/Laplacian/HarmonicForms.lean  # IsHarmonic
  - archive/Hodge/Analytic/HodgeLaplacian.lean           # hodgeLaplacian_ker_iff placeholder
```

## Current State

We have (in archive):
- `IsHarmonic ω := Δω = 0` — definition of harmonic
- Placeholder: `hodgeLaplacian_ker_iff := trivial`

## What It Should Be

The fundamental characterization of harmonic forms:

```lean
theorem harmonic_iff_closed_and_coclosed (ω : SmoothForm n X k) :
    Δω = 0 ↔ (dω = 0 ∧ δω = 0)
```

Or equivalently:
```lean
theorem IsHarmonic_iff_closed_and_coclosed (hk : 1 ≤ k) (hk' : k ≤ n) (ω : SmoothForm n X k) :
    IsHarmonic hk hk' ω ↔ (IsFormClosed ω ∧ IsCoclosed ω)
```

## Proof Strategy

### (⟸) Easy direction
If `dω = 0` and `δω = 0`, then `Δω = dδω + δdω = d(0) + δ(0) = 0`.

### (⟹) Hard direction
Requires the nonnegativity from N4:
```
0 = ⟪Δω, ω⟫ = ‖dω‖² + ‖δω‖²
```
Since both terms are ≥ 0 and sum to 0, each is 0, so `dω = 0` and `δω = 0`.

This requires:
1. The L² norm is positive definite: `‖α‖² = 0 → α = 0`
2. The decomposition `⟪Δω, ω⟫ = ‖dω‖² + ‖δω‖²` from N4

## Definition of Done

- [ ] `harmonic_iff_closed_and_coclosed` is proved (not `trivial`)
- [ ] Connects to existing `IsHarmonic` and `IsFormClosed` predicates
- [ ] `lake build Hodge` succeeds
- [ ] No new axioms introduced

## Progress Log

(Add entries as you work)

- [ ] Started investigation
- [ ] Verified N4 (nonnegativity) is available
- [ ] Proved easy direction (⟸)
- [ ] Proved hard direction (⟹)
- [ ] Verified build passes

---
**When this is complete, check off D.3 in `docs/REQUEUE_ANALYTIC_HODGE_STACK.md`**
