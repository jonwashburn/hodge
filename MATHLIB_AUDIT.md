# Exhaustive Mathlib Audit for Hodge Conjecture Formalization

## Summary

This document catalogs all Mathlib resources relevant to the Hodge Conjecture formalization.

---

## 1. DIFFERENTIAL FORMS & EXTERIOR DERIVATIVE ✅ EXCELLENT

**Location:** `Mathlib.Analysis.Calculus.DifferentialForm.Basic`

| Definition/Theorem | Description | Status |
|-------------------|-------------|--------|
| `extDeriv` | Exterior derivative on normed spaces | ✅ Available |
| `extDeriv_extDeriv` | **d² = 0** | ✅ **PROVED** |
| `extDeriv_add` | d(ω₁ + ω₂) = dω₁ + dω₂ | ✅ Available |
| `extDeriv_smul` | d(c•ω) = c•dω | ✅ Available |
| `extDerivWithin_pullback` | Pullback commutes with d | ✅ Available |

**Usage:** Replace axiomatized `d_squared_zero` with Mathlib's `extDeriv_extDeriv`.

---

## 2. CONVEX CONES ✅ EXCELLENT

**Location:** `Mathlib.Analysis.Convex.Cone.*`

| Definition/Theorem | Description | Status |
|-------------------|-------------|--------|
| `ConvexCone` | Convex cone structure | ✅ Available |
| `ProperCone` | Pointed, closed convex cone | ✅ Available |
| `PointedCone` | Pointed cone | ✅ Available |
| `ConvexCone.hull` | Convex cone hull of a set | ✅ Available |
| `hyperplane_separation` | Separation theorems | ✅ Available |
| `innerDual` | Inner product dual cone | ✅ Available |
| `isClosed_dual` | Dual cone is closed | ✅ Available |

**Usage:** Use for `stronglyPositiveCone` and calibrated cone definitions.

---

## 3. CARATHÉODORY THEOREM ✅ EXCELLENT

**Location:** `Mathlib.Analysis.Convex.Caratheodory`

| Theorem | Description | Status |
|---------|-------------|--------|
| `convexHull_eq_union` | Convex hull characterization | ✅ Available |
| `eq_pos_convex_span_of_mem_convexHull` | Positive span representation | ✅ Available |
| `affineIndependent_minCardFinsetOfMemConvexHull` | Affine independence | ✅ Available |

**Usage:** Can replace axiom `conic_combination_exists` in `Cone.lean`.

---

## 4. EXTERIOR ALGEBRA ✅ GOOD

**Location:** `Mathlib.LinearAlgebra.ExteriorAlgebra.*`

| Definition | Description | Status |
|------------|-------------|--------|
| `ExteriorAlgebra` | Exterior algebra ⋀E | ✅ Available |
| `ExteriorAlgebra.Grading` | Graded structure | ✅ Available |
| `AlternatingMap` | k-linear alternating maps | ✅ Available |
| `ContinuousAlternatingMap` | Continuous version | ✅ Available |

**Location:** `Mathlib.LinearAlgebra.Alternating.*`

| Definition | Description | Status |
|------------|-------------|--------|
| `AlternatingMap.curry` | Currying alternating maps | ✅ Available |
| `AlternatingMap.domCoprod` | Domain coproduct | ✅ Available |

---

## 5. INNER PRODUCT SPACES ✅ EXCELLENT

**Location:** `Mathlib.Analysis.InnerProductSpace.*`

| Definition/Theorem | Description | Status |
|-------------------|-------------|--------|
| `orthogonalProjection` | Orthogonal projection | ✅ Available |
| `starProjection` | Star projection | ✅ Available |
| `GramSchmidtOrtho` | Gram-Schmidt orthogonalization | ✅ Available |
| `Laplacian` | Laplacian operator | ✅ Available |
| `Harmonic` | Harmonic functions | ✅ Available |
| `Adjoint` | Adjoint operators | ✅ Available |

**Usage:** Use for Hodge star, Laplacian, harmonic forms.

---

## 6. SHEAF COHOMOLOGY ✅ AVAILABLE (Limited)

**Location:** `Mathlib.CategoryTheory.Sites.SheafCohomology.*`

| Definition | Description | Status |
|------------|-------------|--------|
| `Sheaf.H` | Sheaf cohomology H^n(F) | ✅ Available |
| `cohomologyPresheafFunctor` | Cohomology presheaf | ✅ Available |

**Note:** Defined via Ext-groups. May need adaptation for coherent sheaves.

**Location:** `Mathlib.Topology.Sheaves.*`

| Definition | Description | Status |
|------------|-------------|--------|
| `Sheaf` | Sheaf on a site | ✅ Available |
| `presheafToSheaf` | Sheafification | ✅ Available |

---

## 7. COMPLEX MANIFOLDS ⚠️ PARTIAL

**Location:** `Mathlib.Geometry.Manifold.Complex`

| Theorem | Description | Status |
|---------|-------------|--------|
| `MDifferentiable.isLocallyConstant` | Holomorphic on compact → locally constant | ✅ Available |
| `MDifferentiable.exists_eq_const_of_compactSpace` | Holomorphic on compact connected → constant | ✅ Available |

**TODO in Mathlib (noted in source):**
- Holomorphic vector/line bundles ❌
- Finite-dimensionality of sections ❌  
- Siegel's theorem ❌
- Weierstrass preparation theorem ❌

---

## 8. RIEMANNIAN GEOMETRY ⚠️ PARTIAL

**Location:** `Mathlib.Geometry.Manifold.Riemannian.*`

| Definition | Description | Status |
|------------|-------------|--------|
| `Riemannian.Basic` | Basic Riemannian structure | ✅ Available |
| `PathELength` | Path length | ✅ Available |

**Missing:** Kähler manifolds, Kähler form, Kähler identities.

---

## 9. VECTOR BUNDLES ✅ GOOD

**Location:** `Mathlib.Geometry.Manifold.VectorBundle.*`

| Definition | Description | Status |
|------------|-------------|--------|
| `VectorBundle.Basic` | Vector bundle structure | ✅ Available |
| `VectorBundle.Tangent` | Tangent bundle | ✅ Available |
| `VectorBundle.Pullback` | Pullback bundles | ✅ Available |
| `VectorBundle.Hom` | Hom bundles | ✅ Available |
| `SmoothSection` | Smooth sections | ✅ Available |

**Missing:** Line bundles, ample bundles, holomorphic bundles.

---

## 10. ALGEBRAIC GEOMETRY ⚠️ PARTIAL

**Location:** `Mathlib.AlgebraicGeometry.*`

| Definition | Description | Status |
|------------|-------------|--------|
| `Scheme` | Schemes | ✅ Available |
| `ProjectiveSpectrum` | Projective spectrum | ✅ Available |
| `IdealSheaf` | Ideal sheaves | ✅ Available |
| `Gluing` | Scheme gluing | ✅ Available |

**Missing:** GAGA theorem, Chow's theorem, algebraic cycles.

---

## 11. GRASSMANNIAN ⚠️ MINIMAL

**Location:** `Mathlib.RingTheory.Grassmannian`

Only basic ring-theoretic Grassmannian. Missing:
- Complex Grassmannian Gr(p, n) ❌
- Calibrated Grassmannian ❌
- Plücker embedding ❌

---

## 12. MEASURE THEORY / GMT ⚠️ PARTIAL

**Location:** `Mathlib.MeasureTheory.*`

| Definition | Description | Status |
|------------|-------------|--------|
| `Measure` | Measures | ✅ Available |
| `Haar measure` | Haar measure on groups | ✅ Available |
| `Integral` | Integration | ✅ Available |

**Missing:**
- Currents ❌
- Integral currents ❌
- Flat norm ❌
- Federer-Fleming compactness ❌
- Harvey-Lawson theorem ❌

---

## PRIORITY INTEGRATION RECOMMENDATIONS

### Immediate (Replace Axioms):

1. **`extDeriv_extDeriv`** → Replace `d_squared_zero` axiom
2. **`ConvexCone.hull`** → Use for `stronglyPositiveCone` 
3. **Carathéodory** → Replace `conic_combination_exists` axiom
4. **`orthogonalProjection`** → Use for Hodge decomposition
5. **`Laplacian`** → Replace axiomatized Laplacian

### Medium Priority (Enhance Definitions):

6. **`ProperCone`** → Use for calibrated cones
7. **`SmoothSection`** → Use for holomorphic sections
8. **`Sheaf.H`** → Adapt for coherent sheaf cohomology

### Long-term (Infrastructure Gaps):

9. **Kähler manifolds** - Need to define
10. **Line bundles** - Need to define  
11. **Currents** - Need to define (GMT)
12. **Harvey-Lawson** - Remains axiom (deep result)
13. **GAGA** - Remains axiom (deep result)

---

## AXIOMS THAT CAN BE REMOVED

Based on Mathlib availability:

| Current Axiom | Mathlib Replacement |
|---------------|---------------------|
| `d_squared_zero` | `extDeriv_extDeriv` |
| `conic_combination_exists` | Carathéodory + `ConvexCone.hull` |
| Laplacian definition | `Laplacian` from InnerProductSpace |
| Orthogonal projection | `orthogonalProjection` |

## AXIOMS THAT MUST REMAIN

| Axiom | Reason |
|-------|--------|
| `harvey_lawson_theorem` | Deep result not in Mathlib |
| `serre_gaga` | GAGA not in Mathlib |
| `serre_vanishing` | Sheaf cohomology vanishing |
| `jet_surjectivity` | Bergman geometry not in Mathlib |
| `tian_convergence` | Complex geometry not in Mathlib |
| `federer_fleming_compactness` | GMT not in Mathlib |


