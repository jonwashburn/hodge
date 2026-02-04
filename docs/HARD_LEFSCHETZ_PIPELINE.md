# Hard Lefschetz Pipeline

**Author**: Agent 4 (sl(2) and Hard Lefschetz)  
**Last Updated**: 2026-01-20  
**Status**: Complete - Classical Pillar Approach

---

## Overview

This document describes the Hard Lefschetz Theorem formalization in the Hodge project,
including the sl(2) representation theory approach and its connection to Kähler identities.

---

## Mathematical Background

### The Hard Lefschetz Theorem

On a compact Kähler manifold $X$ of complex dimension $n$, with Kähler form $\omega$:

**Theorem (Hard Lefschetz, 1924)**:  
For $k \leq n$, the iterated Lefschetz operator
$$L^{n-k} : H^k(X, \mathbb{C}) \to H^{2n-k}(X, \mathbb{C})$$
defined by $L(\alpha) = [\omega] \smile \alpha$ is an isomorphism.

### Why It Matters

Hard Lefschetz is fundamental because it:
1. Provides structure to cohomology of Kähler manifolds
2. Enables the Lefschetz (primitive) decomposition
3. Is essential for Hodge-Riemann bilinear relations
4. Underpins the proof of the Hodge conjecture's statement

---

## The sl(2) Representation Theory Approach

### The sl(2) Triple

On a compact Kähler manifold, three operators form an sl(2,ℂ) representation:

| Operator | Definition | Degree Change |
|----------|------------|---------------|
| **L** (Lefschetz) | $L(\alpha) = \omega \wedge \alpha$ | $+2$ |
| **Λ** (dual Lefschetz) | Formal adjoint of $L$ | $-2$ |
| **H** (weight) | $H = [L, \Lambda] = (k - n) \cdot \text{Id}$ on $H^k$ | $0$ |

### Commutation Relations

These operators satisfy the sl(2) Lie algebra relations:
$$[H, L] = 2L, \quad [H, \Lambda] = -2\Lambda, \quad [L, \Lambda] = H$$

### Representation Theory Proof Strategy

1. **Establish Kähler identities**: $[\Lambda, d] = i\bar{\partial}^*$, $[L, d^*] = -i\bar{\partial}$
2. **Show $(L, \Lambda, H)$ satisfy sl(2) relations** on harmonic forms
3. **Apply finite-dimensional sl(2) representation theory**:
   - Each irreducible sl(2) representation has a unique highest weight vector
   - $L^{n-k}$ is bijective by representation theory

---

## Formalization Structure

### Files Involved

| File | Purpose |
|------|---------|
| `Hodge/Kahler/Lefschetz/Sl2Representation.lean` | Core bijectivity statement |
| `Hodge/Kahler/Lefschetz/PrimitiveDecomp.lean` | Primitive decomposition |
| `Hodge/Kahler/Lefschetz/Sl2.lean` | sl(2) commutation relations |
| `Hodge/Kahler/Identities/LambdaD.lean` | $[\Lambda, d]$ identity |
| `Hodge/Kahler/Identities/LDelta.lean` | $[L, \delta]$ identity |
| `Hodge/Classical/Lefschetz.lean` | Hard Lefschetz equivalence |

### Key Definitions

#### 1. Kähler Class (`kahlerClass`)

```lean
noncomputable def kahlerClass : DeRhamCohomologyClass n X 2 :=
  ⟦K.omega_form, K.omega_closed⟧
```

The cohomology class of the Kähler form.

#### 2. Lefschetz Power (`lefschetzPower`)

```lean
noncomputable def lefschetzPower (p r : ℕ) :
    DeRhamCohomologyClass n X p →ₗ[ℂ] DeRhamCohomologyClass n X (p + 2 * r) :=
  lefschetz_power_of_class (n := n) (X := X) (ω := kahlerClass) p r
```

The iterated Lefschetz operator $L^r$ on cohomology.

#### 3. Hard Lefschetz Data (`HardLefschetzData`)

```lean
class HardLefschetzData (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] : Prop where
  bijective : ∀ k : ℕ, k ≤ n →
    Function.Bijective (lefschetzPower (n := n) (X := X) (p := k) (r := n - k))
```

A Classical Pillar typeclass encapsulating the Hard Lefschetz bijectivity.

---

## Classical Pillar Status

The Hard Lefschetz Theorem is formalized as a **Classical Pillar**:

| Aspect | Status |
|--------|--------|
| Statement | ✅ Fully stated |
| Interface | ✅ `HardLefschetzData` typeclass |
| Proof | ⚠️ Off proof track (would require ~6-12 months) |
| Usage | ✅ Used in main proof via typeclass assumption |

### Why a Classical Pillar?

A complete formal proof of Hard Lefschetz requires:

1. **Kähler Identities** (Hodge theory):
   - $[\Lambda, \partial] = -i\partial^*$
   - $[\Lambda, \bar{\partial}] = i\bar{\partial}^*$
   - These require the full Hodge star and codifferential

2. **Harmonic Representatives** (Hodge decomposition):
   - Every cohomology class has a unique harmonic representative
   - Requires spectral theory of the Laplacian

3. **Primitive Decomposition**:
   - $H^k(X) = \bigoplus_{r \geq 0} L^r P^{k-2r}$
   - Where $P^j = \ker(\Lambda|_{H^j})$

4. **sl(2) Representation Theory**:
   - Finite-dimensional representation classification
   - Highest weight theory

**Estimated effort**: 6-12 months of formalization work.

---

## Connection to Kähler Identities

### Logical Flow

```
Kähler Identities (off track)
        ↓
  [Λ, d] = i∂̄*, [L, δ] = -i∂̄
        ↓
sl(2) Commutation Relations
        ↓
Finite-dim sl(2) Rep Theory
        ↓
  L^{n-k} is bijective
        ↓
Hard Lefschetz Theorem
```

### Current Implementation

The Kähler identities are currently placeholder stubs:

```lean
-- In Hodge/Kahler/Identities/LambdaD.lean
noncomputable def commutator_Lambda_d (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k - 1) := ...

theorem kahler_identity_Lambda_d (k : ℕ) :
    commutator_Lambda_d k =
      Complex.I • (dolbeaultBarStar k - dolbeaultStar k) := ...
```

These compile but use placeholder operators (`lefschetzLambda := 0`, etc.).

---

## Primitive Decomposition

### Primitive Cohomology

A cohomology class $\alpha \in H^k(X)$ is **primitive** if $\Lambda(\alpha) = 0$.

```lean
def PrimitiveCohomology (k : ℕ) (hk : k ≥ 2) : Submodule ℂ (DeRhamCohomologyClass n X k) :=
  LinearMap.ker (lefschetzLambda_cohomology hk)
```

### Lefschetz Decomposition

**Theorem**: Every $\alpha \in H^k(X)$ decomposes uniquely as:
$$\alpha = \sum_{r \geq 0} L^r(\alpha_r)$$
where $\alpha_r \in P^{k-2r}$ is primitive.

### Current Status

The primitive decomposition infrastructure exists but uses placeholder operators:
- `lefschetzLambda := 0` (dual Lefschetz on forms)
- `lefschetzLambda_cohomology := 0` (dual Lefschetz on cohomology)

---

## Test Coverage

The test file `Hodge/Kahler/Lefschetz/LefschetzTests.lean` verifies:

1. **sl(2) relations compile** - The operator definitions typecheck
2. **Primitive decomposition types** - Submodule definitions work
3. **Hard Lefschetz statement** - The bijectivity statement compiles
4. **Inverse construction** - `LinearEquiv.ofBijective` works with `HardLefschetzData`

---

## Usage in Main Proof

The main theorem `hodge_conjecture_data` does **not** directly use Hard Lefschetz:

- Hard Lefschetz is part of the background Kähler geometry infrastructure
- The main proof path uses GMT (currents, calibrations) rather than Hodge theory
- The `HardLefschetzData` typeclass is available if future work needs it

---

## References

1. **Lefschetz, S.** (1924). *L'analysis situs et la géométrie algébrique*.
2. **Griffiths, P. & Harris, J.** (1978). *Principles of Algebraic Geometry*, Ch. 0, §6-7.
3. **Voisin, C.** (2002). *Hodge Theory and Complex Algebraic Geometry I*, Ch. 5-6.
4. **Huybrechts, D.** (2005). *Complex Geometry: An Introduction*, Ch. 3.

---

## Appendix: Key Type Signatures

### `sl2_representation_bijectivity`

```lean
theorem sl2_representation_bijectivity (k : ℕ) (hk : k ≤ n)
    [HardLefschetzData (n := n) (X := X)] :
    Function.Bijective (lefschetzPower (n := n) (X := X) (p := k) (r := n - k)) :=
  HardLefschetzData.bijective (n := n) (X := X) k hk
```

### `hard_lefschetz_equiv`

```lean
noncomputable def hard_lefschetz_equiv {k : ℕ} (hk : k ≤ n) [HardLefschetzData n X] :
    DeRhamCohomologyClass n X k ≃ₗ[ℂ] DeRhamCohomologyClass n X (k + 2 * (n - k)) :=
  LinearEquiv.ofBijective
    (lefschetz_power_cohomology (n - k))
    (hard_lefschetz_from_sl2 hk)
```

### `lefschetz_inverse_cohomology`

```lean
noncomputable def lefschetz_inverse_cohomology {k : ℕ} (hk : k ≤ n) [HardLefschetzData n X] :
    DeRhamCohomologyClass n X (k + 2 * (n - k)) →ₗ[ℂ] DeRhamCohomologyClass n X k :=
  (hard_lefschetz_equiv hk).symm.toLinearMap
```
