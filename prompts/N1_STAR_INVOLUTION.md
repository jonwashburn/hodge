# N1: Prove Hodge Star Involution (⋆⋆ = ±id)

**Re-queue this prompt until the checkbox is checked.**

> **Prerequisites**: M1-M4 (MUST-HAVE semantic validity) should be complete first.
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
  ./scripts/audit_stubs.sh                        # Audit for stubs/sorries

## Key Files for This Task
  - Hodge/Analytic/HodgeStar/FiberStar.lean    # Main star implementation
  - Hodge/Analytic/HodgeStar/Involution.lean   # Skeleton to replace
  - Hodge/Analytic/Norms.lean                  # Section-level star
```

## Current State

**File**: `Hodge/Analytic/HodgeStar/Involution.lean` (skeleton)

```lean
-- Outdated: refers to 2n-k target, but current star is k → (n-k)
theorem fiberHodgeStar_involution (n k : ℕ) (_hk : k ≤ 2 * n) (α : FiberAlt n k) :
    fiberHodgeStar_construct n (2 * n - k) (fiberHodgeStar_construct n k α) = 0 := by
  simp [fiberHodgeStar_construct]
```

The current `fiberHodgeStarCLM` in `FiberStar.lean` maps `k → (n-k)`, so:
- `⋆ : FiberAlt n k → FiberAlt n (n-k)`
- `⋆ : FiberAlt n (n-k) → FiberAlt n (n-(n-k)) = FiberAlt n k`

## What It Should Be

The classical Hodge star involution on an n-dimensional space:

```
⋆(⋆α) = (-1)^{k(n-k)} α
```

For the current implementation:
```lean
theorem fiberHodgeStar_involution (n k : ℕ) (hk : k ≤ n) (α : FiberAlt n k) :
    fiberHodgeStar_construct n (n - k) (fiberHodgeStar_construct n k α) =
      ((-1 : ℤ) ^ (k * (n - k)) : ℂ) • α
```

## Proof Strategy

1. **Expand** `fiberHodgeStarCLM` definition (sum over k-subsets)
2. **Apply star twice**: each basis element `e_I` maps to `ε(I,Iᶜ) e_{Iᶜ}`, then to `ε(Iᶜ,I) e_I`
3. **Compute sign**: `ε(I,Iᶜ) · ε(Iᶜ,I) = (-1)^{k(n-k)}`
4. **Conclude**: the composition is scalar multiplication by the sign

Key lemmas needed:
- `shuffleSign_complement`: `shuffleSign n (finsetComplement n s) * shuffleSign n s = (-1)^{k(n-k)}`
- Basis orthonormality: `fiberBasisForm s` evaluated on `fiberFrame t` is `δ_{s,t}`

## Definition of Done

- [ ] `fiberHodgeStar_involution` proves `⋆⋆α = (±1) • α` with correct sign
- [ ] The skeleton file `Involution.lean` is updated (or replaced)
- [ ] `lake build Hodge` succeeds
- [ ] No new axioms introduced

## Progress Log

(Add entries as you work)

- [ ] Started investigation
- [ ] Proved `shuffleSign_complement` lemma
- [ ] Proved basis orthonormality
- [ ] Proved main involution theorem
- [ ] Updated/replaced `Involution.lean`
- [ ] Verified build passes

---
**When this is complete, check off B.1 in `docs/REQUEUE_ANALYTIC_HODGE_STACK.md`**
