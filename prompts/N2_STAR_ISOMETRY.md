# N2: Prove Hodge Star is an Isometry (⟪⋆α, ⋆β⟫ = ⟪α, β⟫)

**Re-queue this prompt until the checkbox is checked.**

> **Prerequisites**: N1 (star involution) recommended first.
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
  - Hodge/Analytic/HodgeStar/FiberStar.lean    # fiberAltInner, fiberHodgeStarCLM
  - Hodge/Analytic/Norms.lean                  # pointwiseInner, hodgeStar
```

## Current State

We have:
- `fiberAltInner n k α β : ℂ` — Hermitian inner product on fiber k-forms
- `fiberHodgeStarCLM n k : FiberAlt n k →L[ℂ] FiberAlt n (n-k)` — the Hodge star

No isometry theorem is currently proved.

## What It Should Be

The Hodge star preserves the inner product:

```lean
theorem fiberHodgeStar_isometry (n k : ℕ) (hk : k ≤ n) (α β : FiberAlt n k) :
    fiberAltInner n (n - k) (fiberHodgeStar_construct n k α) (fiberHodgeStar_construct n k β) =
      fiberAltInner n k α β
```

This follows from the orthonormality of the basis and the definition of ⋆.

## Proof Strategy

1. **Expand** both sides in terms of basis sums
2. **Use** the fact that `⋆e_I = ε(I,Iᶜ) e_{Iᶜ}` maps the orthonormal basis to another orthonormal basis
3. **Show** the inner product sums are equal (basis coefficient matching)

Alternatively, use the **wedge-star identity** (if available):
```
⟪α, β⟫ · vol = β ⋏ ⋆(conj α)
```
and the fact that ⋆ is an algebra isomorphism.

## Definition of Done

- [ ] `fiberHodgeStar_isometry` is proved
- [ ] (Optional) Lift to section-level: `hodgeStar_isometry` for `SmoothForm`
- [ ] `lake build Hodge` succeeds
- [ ] No new axioms introduced

## Progress Log

(Add entries as you work)

- [ ] Started investigation
- [ ] Proved fiber-level isometry
- [ ] (Optional) Lifted to section level
- [ ] Verified build passes

---
**When this is complete, check off B.2 in `docs/REQUEUE_ANALYTIC_HODGE_STACK.md`**
