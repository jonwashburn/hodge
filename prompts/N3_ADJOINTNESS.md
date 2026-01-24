# N3: Prove Formal L² Adjointness (⟪dω, η⟫ = ⟪ω, δη⟫)

**Re-queue this prompt until the checkbox is checked.**

> **Prerequisites**: N1-N2 (star properties) and volume measure definition.
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
  - Hodge/Analytic/Integration/L2Inner.lean       # L2Inner_measure
  - archive/Hodge/Analytic/Laplacian/Codifferential.lean  # δ definition
  - Hodge/Analytic/Forms.lean                     # smoothExtDeriv (d)
```

## Current State

We have (in archive):
- `codifferential ω = signFactor • ⋆ d ⋆ ω` — the codifferential δ
- `L2Inner_measure μ α β = ∫ pointwiseInner α β dμ` — the L² inner product

No adjointness theorem is proved.

## What It Should Be

The exterior derivative d and codifferential δ are formal L² adjoints:

```lean
theorem d_adjoint_delta (ω : SmoothForm n X k) (η : SmoothForm n X (k+1)) :
    L2Inner_measure μ (smoothExtDeriv ω) η = L2Inner_measure μ ω (codifferential η)
```

This is the key analytic fact that makes the Hodge Laplacian self-adjoint.

## Proof Strategy

### Classical Proof Sketch
1. **Write** the L² pairing as a top-form integral: `⟪α, β⟫ = ∫_X α ⋏ ⋆β̄`
2. **Use Stokes**: `∫_X d(ω ⋏ ⋆η̄) = 0` (compact manifold, no boundary)
3. **Expand Leibniz**: `d(ω ⋏ ⋆η̄) = dω ⋏ ⋆η̄ + (-1)^k ω ⋏ d(⋆η̄)`
4. **Relate** `d(⋆η̄)` to `⋆(δη̄)` using the sign conventions
5. **Conclude** the adjointness

### In This Repo
The proof requires:
- Stokes theorem for the compact manifold (currently axiomatized for closed submanifolds)
- The wedge-star-L² coherence (item C in the plan)
- Leibniz rule (already proved: `smoothExtDeriv_wedge`)

## Definition of Done

- [ ] `d_adjoint_delta` (or equivalent) is proved
- [ ] The proof uses the existing `codifferential` definition
- [ ] `lake build Hodge` succeeds
- [ ] No new axioms introduced (or minimal, well-documented)

## Progress Log

(Add entries as you work)

- [ ] Started investigation
- [ ] Verified Stokes/boundary infrastructure
- [ ] Proved wedge-star coherence (or used existing)
- [ ] Proved adjointness theorem
- [ ] Verified build passes

---
**When this is complete, check off D.1 in `docs/REQUEUE_ANALYTIC_HODGE_STACK.md`**
