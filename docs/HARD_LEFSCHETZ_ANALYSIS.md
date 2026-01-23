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
| sl(2) relations | `Hodge/Kahler/Lefschetz/PrimitiveDecomp.lean` | Placeholders (`True`) |

### Why Off-Track?

Hard Lefschetz is **not used** in the proof of `hodge_conjecture'`. The main proof uses:
- Rationality of Kähler form (given)
- (p,p)-form structure
- Integration theory

The Hodge Conjecture (as stated) does not require Hard Lefschetz.

## Mathematical Statement

**Hard Lefschetz Theorem** (Lefschetz, 1924):

For a compact Kähler manifold X of complex dimension n, the iterated Lefschetz operator

```
L^k : H^{n-k}(X, ℂ) → H^{n+k}(X, ℂ)
```

defined by `L^k(α) = [ω]^k ∪ α` is an isomorphism for all 0 ≤ k ≤ n.

## Proof Path (Classical)

The classical proof proceeds via sl(2) representation theory:

### Step 1: Define the Operators

- **L** (Lefschetz): `L(α) = [ω] ∪ α` (degree +2)
- **Λ** (dual Lefschetz): contraction with ω (degree -2)
- **H** (weight): `H = [L, Λ]` (degree 0)

### Step 2: sl(2) Commutation Relations

Prove that (L, Λ, H) form an sl(2)-representation:
```
[L, Λ] = H      (defines H)
[H, L] = 2L     (L raises weight by 2)
[H, Λ] = -2Λ    (Λ lowers weight by 2)
```

### Step 3: Weight Eigenspaces

On H^k(X), the weight operator acts as `H = (k - n) · id`.
This means H^k(X) is a weight-(k-n) eigenspace.

### Step 4: Representation Theory

From finite-dimensional sl(2) representation theory:
- Every finite-dimensional sl(2)-module decomposes into irreducibles
- Each irreducible is characterized by its highest weight
- The highest weight vectors are exactly the primitive classes

### Step 5: Hard Lefschetz

For the sl(2)-module structure on H*(X):
- L^{n-k} : H^k → H^{2n-k} maps weight-(k-n) to weight-(n-k)
- This is the standard "raising operator to the power of the weight difference"
- By sl(2) representation theory, this is an isomorphism

## What Would Be Needed

### Required Infrastructure (Estimated: 6-12 months)

1. **Real Λ operator** (not `:= 0`)
   - Needs: metric contraction, Hodge star
   - Location: `Hodge/Kahler/Lefschetz/PrimitiveDecomp.lean`

2. **Kähler identities**
   - `[Λ, d] = i∂̄*`
   - `[L, d*] = -i∂̄`
   - Needs: full Hodge star, adjoint operators

3. **sl(2) commutation proofs**
   - `[L, Λ] = H` (needs real Λ)
   - `[H, L] = 2L`
   - `[H, Λ] = -2Λ`

4. **Finite-dimensional sl(2) representation theory**
   - Highest weight modules
   - Decomposition into irreducibles
   - Could use Mathlib's representation theory

5. **Application to cohomology**
   - H*(X) as sl(2)-module
   - Primitive decomposition

### Key Dependencies

```
Hard Lefschetz
    ↑
sl(2) bijectivity theorem
    ↑
sl(2) representation theory (Mathlib?)
    ↑
sl(2) relations for (L, Λ, H)
    ↑
Real Λ operator
    ↑
Hodge star operator
    ↑
Metric infrastructure
```

## Current Workaround

The `HardLefschetzData` typeclass packages the bijectivity assumption:

```lean
class HardLefschetzData (n : ℕ) (X : Type u) ... : Prop where
  bijective : ∀ k : ℕ, k ≤ n →
    Function.Bijective (lefschetzPower (n := n) (X := X) (p := k) (r := n - k))
```

This allows:
- Clean separation from main proof track
- Future upgradeability when sl(2) proof is available
- No "hidden axioms" in `KahlerManifold`

## References

1. Lefschetz, S. (1924). "L'analysis situs et la géométrie algébrique"
2. Griffiths, P. & Harris, J. (1978). "Principles of Algebraic Geometry", Ch. 0
3. Voisin, C. (2002). "Hodge Theory and Complex Algebraic Geometry I", Ch. 5-6
4. Wells, R.O. (1973). "Differential Analysis on Complex Manifolds"

## Files

| File | Purpose |
|------|---------|
| `Hodge/Cohomology/Basic.lean` | KahlerManifold class (no HL) |
| `Hodge/Kahler/Lefschetz/Sl2Representation.lean` | HardLefschetzData class |
| `Hodge/Kahler/Lefschetz/PrimitiveDecomp.lean` | Infrastructure (L, Λ, H, primitives) |
| `Hodge/Classical/Lefschetz.lean` | LinearEquiv from bijectivity |

---

*Last updated: 2026-01-23*
*Author: Agent (Hard Lefschetz Analysis)*
