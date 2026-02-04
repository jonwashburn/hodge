# Hard Lefschetz Theorem: Analysis and Proof Path

## Current Status

The Hard Lefschetz theorem is **intentionally off the proof track** for `hodge_conjecture_data`.

| Component | Location | Status |
|-----------|----------|--------|
| `KahlerManifold` class | `Hodge/Cohomology/Basic.lean` | ✅ No Hard Lefschetz field |
| `HardLefschetzData` class | `Hodge/Kahler/Lefschetz/Sl2Representation.lean` | Assumption package |
| Lefschetz operator L | `Hodge/Cohomology/Basic.lean` | ✅ Defined (cup with [ω]) |

### Why Off-Track?

Hard Lefschetz is **not used** in the proof of `hodge_conjecture_data`. The main proof uses:
- Rationality of Kähler form (given)
- (p,p)-form structure
- Integration theory

## Mathematical Statement

**Hard Lefschetz Theorem** (Lefschetz, 1924):

For a compact Kähler manifold X of complex dimension n, the iterated Lefschetz operator
L^k : H^{n-k}(X, ℂ) → H^{n+k}(X, ℂ) defined by L^k(α) = [ω]^k ∪ α
is an isomorphism for all 0 ≤ k ≤ n.

## Proof Path (Classical)

The classical proof proceeds via sl(2) representation theory:

1. **Define Operators**: L (Lefschetz), Λ (dual), H (weight)
2. **sl(2) Relations**: [L, Λ] = H, [H, L] = 2L, [H, Λ] = -2Λ
3. **Representation Theory**: Apply finite-dimensional sl(2) theory
4. **Conclude**: L^{n-k} is bijective

## Required Infrastructure (6-12 months)

1. Real Λ operator (needs Hodge star)
2. Kähler identities
3. sl(2) commutation proofs
4. sl(2) representation theory

## References

1. Lefschetz (1924). "L'analysis situs et la géométrie algébrique"
2. Griffiths & Harris (1978). "Principles of Algebraic Geometry", Ch. 0
3. Voisin (2002). "Hodge Theory and Complex Algebraic Geometry I", Ch. 5-6

---
*Last updated: 2026-01-23*
