# Hard Lefschetz Theorem: Analysis and Proof Path

## Current Status

### Architecture Overview

The Hard Lefschetz theorem is **intentionally off the proof track** for `hodge_conjecture'`.

| Component | Location | Status |
|-----------|----------|--------|
| `KahlerManifold` class | `Hodge/Cohomology/Basic.lean` | ✅ No Hard Lefschetz field |
| `HardLefschetzData` class | `Hodge/Kahler/Lefschetz/Sl2Representation.lean` | Assumption package |
| Lefschetz operator L | `Hodge/Cohomology/Basic.lean` | ✅ Defined (cup with [ω]) |
| Dual Lefschetz Λ | `Hodge/Kahler/Lefschetz/PrimitiveDecomp.lean` | `:= 0` placeholder |
| Weight operator H | `Hodge/Kahler/Lefschetz/PrimitiveDecomp.lean` | Defined as (k-n)·id |
| sl(2) relations | `Hodge/Kahler/Lefschetz/PrimitiveDecomp.lean` | Placeholders |

### Why Off-Track?

Hard Lefschetz is **not used** in the proof of `hodge_conjecture'`. The main proof uses:
- Rationality of Kähler form (given)
- (p,p)-form structure
- Integration theory

The Hodge Conjecture (as stated) does not require Hard Lefschetz.

## Mathematical Statement

**Hard Lefschetz Theorem** (Lefschetz, 1924):

For a compact Kähler manifold X of complex dimension n, the iterated Lefschetz operator
L^k : H^{n-k}(X, ℂ) → H^{n+k}(X, ℂ) defined by L^k(α) = [ω]^k ∪ α
is an isomorphism for all 0 ≤ k ≤ n.

## Proof Path (Classical)

The classical proof proceeds via sl(2) representation theory:

### Step 1: Define the Operators

- **L** (Lefschetz): L(α) = [ω] ∪ α (degree +2)
- **Λ** (dual Lefschetz): contraction with ω (degree -2)
- **H** (weight): H = [L, Λ] (degree 0)

### Step 2: sl(2) Commutation Relations

Prove that (L, Λ, H) form an sl(2)-representation:
- [L, Λ] = H (defines H)
- [H, L] = 2L (L raises weight by 2)
- [H, Λ] = -2Λ (Λ lowers weight by 2)

### Step 3: Weight Eigenspaces

On H^k(X), the weight operator acts as H = (k - n) · id.

### Step 4: Representation Theory

From finite-dimensional sl(2) representation theory:
- Every finite-dimensional sl(2)-module decomposes into irreducibles
- The highest weight vectors are exactly the primitive classes

### Step 5: Hard Lefschetz

L^{n-k} : H^k → H^{2n-k} is an isomorphism by sl(2) representation theory.

## What Would Be Needed (6-12 months estimated)

1. **Real Λ operator** - needs metric contraction, Hodge star
2. **Kähler identities** - [Λ, d] = i∂̄*, [L, d*] = -i∂̄
3. **sl(2) commutation proofs**
4. **Finite-dimensional sl(2) representation theory** (Mathlib?)
5. **Application to cohomology**

## Current Workaround

The HardLefschetzData typeclass packages the bijectivity assumption separately.

## References

1. Lefschetz, S. (1924). "L'analysis situs et la géométrie algébrique"
2. Griffiths & Harris (1978). "Principles of Algebraic Geometry", Ch. 0
3. Voisin (2002). "Hodge Theory and Complex Algebraic Geometry I", Ch. 5-6

---
*Last updated: 2026-01-23*
