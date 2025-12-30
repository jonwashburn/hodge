# Hodge Conjecture Lean Formalization: Full Sprint Plan

**Generated:** 2024-12-30  
**Build Status:** ❌ Errors in `Hodge/Kahler/SignedDecomp.lean` (7 errors)  
**Total Axioms/Opaques:** 196  
**Target:** Convert all to theorems/defs (except ~12 classical pillars)

---

## 🎯 MISSION STATEMENT

We are building a **complete, unconditional, machine-checkable proof** of the Hodge Conjecture in Lean 4. Every axiom must be converted to a theorem. Every opaque must become a concrete definition.

---

## 🚫 ABSOLUTE RULES

| Rule | Details |
|------|---------|
| **NO `sorry`** | Leaves proof incomplete |
| **NO `admit`** | Same as sorry |
| **NO builds** | Only the coordinator runs builds. Agents write code. |
| **Mathlib first** | Search before writing custom lemmas |
| **Document everything** | Every non-obvious step needs a comment |

---

## 📜 AXIOM POLICY

### ✅ ALLOWED TO REMAIN AS AXIOMS (Classical Pillars)

| Axiom | Reference |
|-------|-----------|
| `hard_lefschetz_inverse_form` | Lefschetz 1924, Hodge 1941 |
| `serre_gaga` | Serre 1956 |
| `harvey_lawson_theorem` | Harvey-Lawson 1982 |
| `federer_fleming_compactness` | Federer-Fleming 1960 |
| `tian_convergence` | Tian 1990 |
| `barany_grinberg` | Bárány-Grinberg 1981 |

### ❌ MUST BE CONVERTED TO THEOREMS

Everything else. This includes:
- All `isSmoothAlternating_*` axioms
- All `smoothExtDeriv_*` axioms  
- All `pointwiseComass_*` axioms
- All `mass_*` axioms
- All `flatNorm_*` axioms
- All `isRationalClass_*` axioms
- All microstructure axioms
- All cohomology axioms

---

## 📊 AXIOM DISTRIBUTION BY FILE

| File | Axioms/Opaques | Assigned To |
|------|----------------|-------------|
| `Hodge/Kahler/Microstructure.lean` | 24 | Agent 5 |
| `Hodge/Basic.lean` | 20 | Agent 1 |
| `Hodge/Analytic/Norms.lean` | 19 | Agent 1 |
| `Hodge/Classical/GAGA.lean` | 18 | Agent 4 |
| `Hodge/Analytic/Forms.lean` | 14 | Agent 1 |
| `Hodge/Classical/HarveyLawson.lean` | 10 | Agent 4 |
| `Hodge/Classical/Bergman.lean` | 10 | Agent 4 |
| `Hodge/Analytic/SheafTheory.lean` | 10 | Agent 4 |
| `Hodge/Analytic/Grassmannian.lean` | 10 | Agent 3 |
| `Hodge/Kahler/TypeDecomposition.lean` | 9 | Agent 3 |
| `Hodge/Kahler/Manifolds.lean` | 9 | Agent 3 |
| `Hodge/Analytic/FlatNorm.lean` | 9 | Agent 2 |
| `Hodge/Analytic/IntegralCurrents.lean` | 8 | Agent 2 |
| `Hodge/Classical/Lefschetz.lean` | 5 | Agent 4 |
| `Hodge/Analytic/Currents.lean` | 5 | Agent 2 |
| `Hodge/Kahler/Cone.lean` | 4 | Agent 3 |
| `Hodge/Analytic/Calibration.lean` | 4 | Agent 2 |
| `Hodge/Kahler/Main.lean` | 3 | Agent 5 |
| `Hodge/Classical/FedererFleming.lean` | 2 | Agent 4 |
| `Hodge/Utils/BaranyGrinberg.lean` | 1 | Agent 5 |
| `Hodge/Kahler/SignedDecomp.lean` | 1 | Agent 5 |
| `Hodge/Classical/SerreVanishing.lean` | 1 | Agent 4 |

---

## 🔧 CURRENT BUILD ERRORS

```
error: Hodge/Kahler/SignedDecomp.lean:89:28: Tactic `rewrite` failed
error: Hodge/Kahler/SignedDecomp.lean:96:8: Tactic `rewrite` failed
error: Hodge/Kahler/SignedDecomp.lean:113:57: unsolved goals
error: Hodge/Kahler/SignedDecomp.lean:128:16: Unknown identifier `inv_mul_lt_iff`
error: Hodge/Kahler/SignedDecomp.lean:127:19: unsolved goals
error: Hodge/Kahler/SignedDecomp.lean:136:35: Type mismatch
error: Hodge/Kahler/SignedDecomp.lean:107:19: unsolved goals
```

Agent 5 must fix these first.

---

# 🤖 AGENT 1: Forms & Norms Infrastructure

## Ownership

| File | Axioms/Opaques |
|------|----------------|
| `Hodge/Basic.lean` | 20 |
| `Hodge/Analytic/Forms.lean` | 14 |
| `Hodge/Analytic/Norms.lean` | 19 |
| **TOTAL** | **53** |

## Full Axiom List

### Hodge/Basic.lean (20 items)

```lean
-- Line 42: Convert to def
opaque IsSmoothAlternating (n : ℕ) (X : Type u) ... : Prop

-- Line 60: Convert to def using Mathlib topology
axiom smoothFormTopologicalSpace_axiom (k : ℕ) : TopologicalSpace (SmoothForm n X k)

-- Lines 66-78: Prove from definition of IsSmoothAlternating
axiom isSmoothAlternating_zero (k : ℕ) : IsSmoothAlternating n X k ⟨0, ...⟩
axiom isSmoothAlternating_add (k : ℕ) (ω η : SmoothForm n X k) : ...
axiom isSmoothAlternating_neg (k : ℕ) (ω : SmoothForm n X k) : ...
axiom isSmoothAlternating_smul (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) : ...
axiom isSmoothAlternating_sub (k : ℕ) (ω η : SmoothForm n X k) : ...

-- Line 211: Convert to def using exterior derivative
opaque smoothExtDeriv {n : ℕ} {X : Type u} ... (ω : SmoothForm n X k) : SmoothForm n X (k + 1)

-- Lines 217-252: Prove from definition
axiom smoothExtDeriv_extDeriv ... : smoothExtDeriv ω x = extDeriv ω x
axiom smoothExtDeriv_add ... : smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂
axiom smoothExtDeriv_smul ... : smoothExtDeriv (c • ω) = c • smoothExtDeriv ω

-- Lines 605-621: Prove as instances using Quotient API
axiom instAddCommGroupDeRhamCohomologyClass : AddCommGroup (DeRhamCohomologyClass n X k)
axiom instModuleDeRhamCohomologyClass : Module ℂ (DeRhamCohomologyClass n X k)
axiom instModuleRealDeRhamCohomologyClass : Module ℝ (DeRhamCohomologyClass n X k)

-- Line 946: Prove wedge product on cohomology
axiom instHMulDeRhamCohomologyClass : HMul (DeRhamCohomologyClass n X k) ...

-- Lines 996-1021: Prove from Quotient.liftOn
axiom ofForm_add ... : ofForm (ω₁ + ω₂) h = ofForm ω₁ h₁ + ofForm ω₂ h₂
axiom ofForm_sub ... : ofForm (ω₁ - ω₂) h = ofForm ω₁ h₁ - ofForm ω₂ h₂
axiom ofForm_smul_rat ... : ofForm (q • ω) h = q • ofForm ω hω
axiom ofForm_smul_real ... : ofForm (r • ω) h = r • ofForm ω hω

-- Line 1048: Convert to def
opaque isRationalClass {n : ℕ} {X : Type u} ... (η : DeRhamCohomologyClass n X k) : Prop
```

### Hodge/Analytic/Forms.lean (14 items)

```lean
-- Lines 25-35: Convert opaques to defs
opaque unitForm : SmoothForm n X 0
opaque wedge {k l : ℕ} (α : SmoothForm n X k) (β : SmoothForm n X l) : SmoothForm n X (k + l)
opaque hodgeStar {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (2 * n - k)

-- Lines 60-120: Prove linearity properties
axiom wedge_add ... : wedge (α + β) γ = wedge α γ + wedge β γ
axiom wedge_smul ... : wedge (c • α) β = c • wedge α β
axiom wedge_assoc ... : wedge (wedge α β) γ = wedge α (wedge β γ)
axiom smoothExtDeriv_wedge ... : smoothExtDeriv (wedge α β) = ...
axiom hodgeStar_add ... : hodgeStar (α + β) = hodgeStar α + hodgeStar β
axiom hodgeStar_smul ... : hodgeStar (r • α) = r • hodgeStar α

-- Lines 125-143: Convert to defs
opaque adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1)
opaque laplacian {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k
opaque lefschetzLambda {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k - 2)

axiom laplacian_add ... : laplacian (α + β) = laplacian α + laplacian β
```

### Hodge/Analytic/Norms.lean (19 items)

```lean
-- Line 22: Convert to def using sSup
opaque pointwiseComass {n : ℕ} {X : Type*} ... (α : SmoothForm n X k) (x : X) : ℝ

-- Lines 27-58: Prove from definition
axiom pointwiseComass_nonneg ... : pointwiseComass α x ≥ 0
axiom pointwiseComass_continuous ... : Continuous (pointwiseComass α)
axiom pointwiseComass_zero ... : pointwiseComass 0 x = 0
axiom pointwiseComass_add_le ... : pointwiseComass (α + β) x ≤ pointwiseComass α x + pointwiseComass β x
axiom pointwiseComass_smul ... : pointwiseComass (c • α) x = |c| * pointwiseComass α x

-- Lines 75-111: Prove from pointwiseComass
axiom comass_bddAbove ... : BddAbove (Set.range (pointwiseComass α))
axiom comass_zero ... : comass (0 : SmoothForm n X k) = 0
axiom comass_add_le ... : comass (α + β) ≤ comass α + comass β
axiom comass_smul ... : comass (c • α) = |c| * comass α
axiom comass_nonneg ... : comass α ≥ 0
axiom comass_eq_zero_iff ... : comass α = 0 ↔ α = 0

-- Lines 130-162: Convert to defs and prove
opaque pointwiseInner {n : ℕ} {X : Type*} ... (α β : SmoothForm n X k) (x : X) : ℝ
axiom pointwiseInner_self_nonneg ... : pointwiseInner α α x ≥ 0
opaque L2Inner ... (α β : SmoothForm n X k) : ℝ
axiom L2Inner_add_left ... : L2Inner (α + β) γ = L2Inner α γ + L2Inner β γ
axiom L2Inner_smul_left ... : L2Inner (c • α) β = c * L2Inner α β

-- Lines 187-199: Prove or keep as deep theorems
axiom energy_minimizer ... : ...
axiom trace_L2_control ... : ∃ C : ℝ, C > 0 ∧ comass α ≤ C * L2NormForm α
```

## Deliverables

- [ ] Convert all 20 `opaque`/`axiom` in `Basic.lean` to `def`/`theorem`
- [ ] Convert all 14 in `Forms.lean`
- [ ] Convert all 19 in `Norms.lean`
- [ ] Total: 53 items
- [ ] Provide complete, compilable code for each

## Key Mathlib References

```
Mathlib.Analysis.Normed.Group.Basic
Mathlib.Analysis.NormedSpace.Basic
Mathlib.Topology.ContinuousFunction.Compact
Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
Mathlib.Analysis.InnerProductSpace.Basic
```

---

# 🤖 AGENT 2: Currents & GMT

## Ownership

| File | Axioms/Opaques |
|------|----------------|
| `Hodge/Analytic/Currents.lean` | 5 |
| `Hodge/Analytic/FlatNorm.lean` | 9 |
| `Hodge/Analytic/IntegralCurrents.lean` | 8 |
| `Hodge/Analytic/Calibration.lean` | 4 |
| **TOTAL** | **26** |

## Full Axiom List

### Hodge/Analytic/Currents.lean (5 items)

```lean
-- Line 110: Convert to def
opaque mass (T : Current n X k) : ℝ

-- Lines 112-115: Prove from definition
axiom mass_nonneg (T : Current n X k) : mass T ≥ 0
axiom mass_zero : mass (0 : Current n X k) = 0
axiom mass_neg (T : Current n X k) : mass (-T) = mass T
axiom mass_add_le (S T : Current n X k) : mass (S + T) ≤ mass S + mass T
```

### Hodge/Analytic/FlatNorm.lean (9 items)

```lean
-- Line 27: Convert to def using infimum
opaque flatNorm {k : ℕ} (T : Current n X k) : ℝ

-- Lines 30-51: Prove from definition
axiom flatNorm_nonneg {k : ℕ} (T : Current n X k) : flatNorm T ≥ 0
axiom flatNorm_zero {k : ℕ} : flatNorm (0 : Current n X k) = 0
axiom flatNorm_eq_zero_iff {k : ℕ} (T : Current n X k) : flatNorm T = 0 ↔ T = 0
axiom flatNorm_neg {k : ℕ} (T : Current n X k) : flatNorm (-T) = flatNorm T
axiom flatNorm_add_le {k : ℕ} (S T : Current n X k) : flatNorm (S + T) ≤ flatNorm S + flatNorm T
axiom flatNorm_le_mass {k : ℕ} (T : Current n X k) : flatNorm T ≤ Current.mass T
axiom eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) : |T ψ| ≤ comass ψ * flatNorm T
axiom flatNorm_boundary_le {k : ℕ} (T : Current n X (k + 1)) : flatNorm (boundary T) ≤ flatNorm T
```

### Hodge/Analytic/IntegralCurrents.lean (8 items)

```lean
-- Line 24-27: Convert to defs
opaque isRectifiable (k : ℕ) (S : Set X) : Prop
axiom isRectifiable_empty (k : ℕ) : isRectifiable k (∅ : Set X)
axiom isRectifiable_union (k : ℕ) (S₁ S₂ : Set X) : isRectifiable k S₁ → isRectifiable k S₂ → isRectifiable k (S₁ ∪ S₂)

-- Lines 33-47: Prove integrality properties
opaque isIntegral {k : ℕ} (T : Current n X k) : Prop
axiom isIntegral_add {k : ℕ} (S T : Current n X k) : isIntegral S → isIntegral T → isIntegral (S + T)
axiom isIntegral_zero_current (k : ℕ) [Nonempty X] : isIntegral (0 : Current n X k)
axiom isIntegral_smul {k : ℕ} (c : ℤ) (T : Current n X k) : isIntegral T → isIntegral (c • T)
axiom isIntegral_boundary {k : ℕ} (T : Current n X (k + 1)) : isIntegral T → isIntegral (boundary T)
```

### Hodge/Analytic/Calibration.lean (4 items)

```lean
-- Lines 36-55: Prove calibration properties
axiom wirtinger_comass_bound (p : ℕ) : comass (omegaPow n X p) ≤ 1
axiom calibration_inequality {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) : T ψ.toFun ≤ mass T

-- Lines 79-85: Keep as classical or prove
axiom spine_theorem {k : ℕ} (T S G : Current n X k) (ψ : CalibratingForm n X k) ...
axiom mass_lsc {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k) : ... mass T_limit ≤ liminf mass(T_i)
```

## Deliverables

- [ ] Convert all 5 in `Currents.lean`
- [ ] Convert all 9 in `FlatNorm.lean`
- [ ] Convert all 8 in `IntegralCurrents.lean`
- [ ] Convert all 4 in `Calibration.lean`
- [ ] Total: 26 items

## Key Definitions Needed

```lean
-- Flat norm definition
def flatNorm (T : Current n X k) : ℝ :=
  sInf { m | ∃ S R, T = S + boundary R ∧ m = mass S + mass R }

-- Mass definition
def mass (T : Current n X k) : ℝ :=
  sSup { |T ψ| / comass ψ | ψ : SmoothForm n X k, comass ψ > 0 }
```

---

# 🤖 AGENT 3: Grassmannian & Cone Geometry

## Ownership

| File | Axioms/Opaques |
|------|----------------|
| `Hodge/Analytic/Grassmannian.lean` | 10 |
| `Hodge/Kahler/Cone.lean` | 4 |
| `Hodge/Kahler/TypeDecomposition.lean` | 9 |
| `Hodge/Kahler/Manifolds.lean` | 9 |
| **TOTAL** | **32** |

## Full Axiom List

### Hodge/Analytic/Grassmannian.lean (10 items)

```lean
-- Lines 44-52: Volume forms
opaque IsVolumeFormOn {n : ℕ} {X : Type*} ... (x : X) (p : ℕ) (V : Submodule ℂ ...) (ω : ...) : Prop
axiom IsVolumeFormOn_nonzero ... : IsVolumeFormOn x p V ω → ω ≠ 0

-- Lines 70-96: Existence and smoothness
axiom exists_volume_form_of_submodule_axiom (p : ℕ) (x : X) (V : Submodule ℂ ...) (hV : finrank V = p) :
    ∃ ω, IsVolumeFormOn x p V ω
axiom simpleCalibratedForm_is_smooth (p : ℕ) (x : X) (V : Submodule ℂ ...) : IsSmoothAlternating ...

-- Lines 142-167: Distance to cone
opaque distToCone (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) : ℝ
axiom distToCone_nonneg (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) : distToCone p α x ≥ 0
opaque coneDefect (p : ℕ) (α : SmoothForm n X (2 * p)) : ℝ
axiom coneDefect_nonneg (p : ℕ) (α : SmoothForm n X (2 * p)) : coneDefect p α ≥ 0
axiom radial_minimization ... : ∃ t_opt, ...
axiom dist_cone_sq_formula ... : (distToCone p α x)^2 = ...
```

### Hodge/Kahler/Cone.lean (4 items)

```lean
-- Lines 66-106: Wirtinger and cone interior
axiom wirtinger_pairing (p : ℕ) (x : X) (ξ : SmoothForm n X (2 * p)) (hξ : ξ ∈ simpleCalibratedForms p x) :
    pointwiseInner (omegaPow_point p x) ξ x = 1
axiom omegaPow_in_interior (p : ℕ) (x : X) : omegaPow_point p x ∈ interior (stronglyPositiveCone p x)
axiom exists_uniform_interior_radius (p : ℕ) [CompactSpace X] [Nonempty X] :
    ∃ r : ℝ, r > 0 ∧ ∀ x, Metric.ball (omegaPow_point p x) r ⊆ stronglyPositiveCone p x
axiom caratheodory_decomposition (p : ℕ) (x : X) (α : SmoothForm n X (2 * p)) (hα : α ∈ stronglyPositiveCone p x) :
    ∃ (ξ : Fin (n.choose p + 1) → SmoothForm n X (2 * p)) (c : Fin (n.choose p + 1) → ℝ), ...
```

### Hodge/Kahler/TypeDecomposition.lean (9 items)

```lean
-- Line 59: Convert to def
opaque isPQForm (n : ℕ) (X : Type u) ... (p q : ℕ) (ω : SmoothForm n X (p + q)) : Prop

-- Lines 72-130: Prove type decomposition properties
axiom zero_is_pq (n : ℕ) (X : Type u) ... (p q : ℕ) : isPQForm n X ... p q 0
axiom isPQForm_wedge ... : isPQForm n X p q α → isPQForm n X r s β → isPQForm n X (p+r) (q+s) (wedge α β)
axiom omega_is_1_1_axiom ... : isPQForm n X 1 1 (K.omega_form)
axiom unitForm_is_0_0 ... : isPQForm n X 0 0 unitForm
axiom omega_pow_is_p_p_axiom ... : isPQForm n X p p (omegaPow n X p)
axiom omega_pow_isClosed (p : ℕ) : isClosed (omegaPow n X p)
axiom omega_pow_is_rational (p : ℕ) : isRationalClass ⟦omegaPow n X p, omega_pow_isClosed p⟧
axiom isClosed_omegaPow_scaled (p : ℕ) : IsFormClosed ((1 / (p.factorial : ℝ)) • omegaPow n X p)
```

### Hodge/Kahler/Manifolds.lean (9 items)

```lean
-- Lines 27-59: Kähler manifold axioms
axiom kahlerMetric_symm (x : X) (v w : TangentSpace ...) : K.kahlerMetric x v w = conj (K.kahlerMetric x w v)
axiom isRationalClass_wedge ... : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂)
axiom isRationalClass_smul_rat ... (q : ℚ) : isRationalClass η → isRationalClass (q • η)
axiom omega_isClosed : IsFormClosed K.omega_form
axiom omega_is_rational : isRationalClass ⟦K.omega_form, omega_isClosed⟧
axiom isRationalClass_add ... : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂)
axiom zero_is_rational {k : ℕ} : isRationalClass (0 : DeRhamCohomologyClass n X k)
axiom unitForm_isClosed : IsFormClosed unitForm
axiom unitForm_is_rational : isRationalClass ⟦unitForm, unitForm_isClosed⟧
```

## Deliverables

- [ ] Convert all 10 in `Grassmannian.lean`
- [ ] Convert all 4 in `Cone.lean`
- [ ] Convert all 9 in `TypeDecomposition.lean`
- [ ] Convert all 9 in `Manifolds.lean`
- [ ] Total: 32 items

---

# 🤖 AGENT 4: Classical Theorems

## Ownership

| File | Axioms/Opaques |
|------|----------------|
| `Hodge/Classical/GAGA.lean` | 18 |
| `Hodge/Classical/HarveyLawson.lean` | 10 |
| `Hodge/Classical/Bergman.lean` | 10 |
| `Hodge/Analytic/SheafTheory.lean` | 10 |
| `Hodge/Classical/Lefschetz.lean` | 5 |
| `Hodge/Classical/FedererFleming.lean` | 2 |
| `Hodge/Classical/SerreVanishing.lean` | 1 |
| **TOTAL** | **56** |

## Full Axiom List

### Hodge/Classical/GAGA.lean (18 items)

```lean
-- Algebraic set axioms (convert to defs with proper structure)
opaque IsAlgebraicSet {n : ℕ} {X : Type*} ... (Z : Set X) : Prop
axiom IsAlgebraicSet_empty : IsAlgebraicSet (∅ : Set X)
axiom IsAlgebraicSet_univ : IsAlgebraicSet (Set.univ : Set X)
axiom IsAlgebraicSet_union : IsAlgebraicSet Z₁ → IsAlgebraicSet Z₂ → IsAlgebraicSet (Z₁ ∪ Z₂)
axiom IsAlgebraicSet_inter : IsAlgebraicSet Z₁ → IsAlgebraicSet Z₂ → IsAlgebraicSet (Z₁ ∩ Z₂)
axiom IsAlgebraicSet_isClosed : IsAlgebraicSet Z → IsClosed Z
axiom IsAlgebraicSet_nontrivial : ∃ Z : Set X, IsAlgebraicSet Z ∧ Z ≠ ∅ ∧ Z ≠ Set.univ

-- Fundamental class axioms
opaque FundamentalClassSet (n : ℕ) (X : Type u) ... (p : ℕ) (Z : Set X) : SmoothForm n X (2 * p)
axiom FundamentalClassSet_isClosed ... : IsFormClosed (FundamentalClassSet n X p Z)
axiom FundamentalClassSet_rational ... : isRationalClass ⟦FundamentalClassSet n X p Z, ...⟧
axiom FundamentalClassSet_intersection_power_eq ...

-- Hyperplane axioms
axiom exists_hyperplane_algebraic : ∃ H : Set X, IsAlgebraicSet H ∧ ...

-- GAGA bridge
axiom IsAlgebraicSet_isAnalyticSet : IsAlgebraicSet Z → IsAnalyticSet Z
axiom serre_gaga : ... -- KEEP AS AXIOM

-- Algebraic intersection
opaque algebraic_intersection_power (_Z : Set X) (k : ℕ) : Set X
axiom algebraic_intersection_power_is_algebraic ...
```

### Hodge/Classical/HarveyLawson.lean (10 items)

```lean
-- Analytic set axioms
opaque IsAnalyticSet {n : ℕ} {X : Type*} ... (S : Set X) : Prop
axiom IsAnalyticSet_empty : IsAnalyticSet (∅ : Set X)
axiom IsAnalyticSet_univ : IsAnalyticSet (Set.univ : Set X)
axiom IsAnalyticSet_union : IsAnalyticSet S₁ → IsAnalyticSet S₂ → IsAnalyticSet (S₁ ∪ S₂)
axiom IsAnalyticSet_inter : IsAnalyticSet S₁ → IsAnalyticSet S₂ → IsAnalyticSet (S₁ ∩ S₂)
axiom IsAnalyticSet_isClosed : IsAnalyticSet S → IsClosed S
axiom IsAnalyticSet_nontrivial : ∃ S : Set X, IsAnalyticSet S ∧ S ≠ ∅ ∧ S ≠ Set.univ

-- Harvey-Lawson theorem
axiom harvey_lawson_theorem ... -- KEEP AS AXIOM
axiom harvey_lawson_represents ...
axiom flat_limit_of_cycles_is_cycle ... -- PROVE THIS
```

### Hodge/Classical/Bergman.lean (10 items)

```lean
-- Holomorphic structures (convert to defs)
opaque partial_deriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1)
opaque partial_bar_deriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1)
opaque log_h {L : HolomorphicLineBundle n X} (h : HermitianMetric L) : SmoothForm n X 0
opaque L2InnerProduct (L : HolomorphicLineBundle n X) ...
opaque log_KM (L : HolomorphicLineBundle n X) ...
opaque SectionsVanishingToOrder (L : HolomorphicLineBundle n X) ...

-- Bergman/Tian axioms
axiom tian_convergence ... -- KEEP AS AXIOM
axiom jet_surjectivity_axiom ...
axiom IsHolomorphic_tensor_axiom ...
```

### Hodge/Analytic/SheafTheory.lean (10 items)

```lean
-- Sheaf cohomology (convert to proper definitions)
opaque SheafCohomology {n : ℕ} {X : Type u} ... (F : CoherentSheaf n X) (q : ℕ) : Type u
axiom SheafCohomology.instAddCommGroup ... : AddCommGroup (SheafCohomology F q)
axiom SheafCohomology.instModule ... : Module ℂ (SheafCohomology F q)
axiom SheafCohomology.finiteDimensional ... : FiniteDimensional ℂ (SheafCohomology F q)

-- Vanishing predicate
opaque vanishes {n : ℕ} {X : Type u} ... (F : CoherentSheaf n X) (q : ℕ) : Prop
axiom vanishes_iff_subsingleton ... : vanishes F q ↔ Subsingleton (SheafCohomology F q)

-- Structure sheaf
opaque structureSheafAsCoherent (n : ℕ) (X : Type u) ... : CoherentSheaf n X
axiom h0_structure_sheaf_nonvanishing ... : ¬ vanishes (structureSheafAsCoherent n X) 0
```

### Hodge/Classical/Lefschetz.lean (5 items)

```lean
axiom hard_lefschetz_isomorphism ... -- KEEP AS AXIOM
axiom hard_lefschetz_inverse_form ... -- KEEP AS AXIOM
axiom lefschetz_on_cohomology ...
axiom lefschetz_inverse_cohomology ...
axiom lefschetz_compatibility ...
```

### Hodge/Classical/FedererFleming.lean (2 items)

```lean
axiom federer_fleming_compactness ... -- KEEP AS AXIOM
axiom deformation_theorem ...
```

### Hodge/Classical/SerreVanishing.lean (1 item)

```lean
axiom serre_vanishing ... -- KEEP AS AXIOM
```

## Deliverables

- [ ] Convert 18 in `GAGA.lean` (keeping `serre_gaga` as axiom)
- [ ] Convert 10 in `HarveyLawson.lean` (keeping `harvey_lawson_theorem` as axiom)
- [ ] Convert 10 in `Bergman.lean` (keeping `tian_convergence` as axiom)
- [ ] Convert 10 in `SheafTheory.lean`
- [ ] Convert 5 in `Lefschetz.lean` (keeping `hard_lefschetz_*` as axioms)
- [ ] Convert 2 in `FedererFleming.lean` (keeping compactness as axiom)
- [ ] Keep 1 in `SerreVanishing.lean` as axiom
- [ ] Total: 56 items (minus ~8 allowed axioms = 48 to convert)

---

# 🤖 AGENT 5: Microstructure & Main Proof

## Ownership

| File | Axioms/Opaques |
|------|----------------|
| `Hodge/Kahler/Microstructure.lean` | 24 |
| `Hodge/Kahler/SignedDecomp.lean` | 1 + **7 ERRORS** |
| `Hodge/Kahler/Main.lean` | 3 |
| `Hodge/Utils/BaranyGrinberg.lean` | 1 |
| **TOTAL** | **29 + fix errors** |

## CRITICAL: Fix Build Errors First

```
error: Hodge/Kahler/SignedDecomp.lean:89:28: Tactic `rewrite` failed
error: Hodge/Kahler/SignedDecomp.lean:96:8: Tactic `rewrite` failed  
error: Hodge/Kahler/SignedDecomp.lean:113:57: unsolved goals
error: Hodge/Kahler/SignedDecomp.lean:128:16: Unknown identifier `inv_mul_lt_iff`
error: Hodge/Kahler/SignedDecomp.lean:127:19: unsolved goals
error: Hodge/Kahler/SignedDecomp.lean:136:35: Type mismatch
error: Hodge/Kahler/SignedDecomp.lean:107:19: unsolved goals
```

## Full Axiom List

### Hodge/Kahler/Microstructure.lean (24 items)

```lean
-- Complex submanifold
opaque IsComplexSubmanifold (Y : Set X) (p : ℕ) : Prop
axiom local_sheet_realization (p : ℕ) (x : X) (ξ : SmoothForm n X (2 * p)) ...

-- Cubulation
axiom cubulation_exists (h : ℝ) (hh : h > 0) : Cubulation n X h

-- Integer approximation
opaque IsValidIntegerApproximation ... : Prop
axiom IsValidIntegerApproximation_edge_bound ...
axiom integer_transport (p : ℕ) {h : ℝ} (C : Cubulation n X h) (target : Flow C) : ∃ int_flow, IsValidIntegerApproximation ...

-- Gluing
opaque IsValidGluing ... : Prop
axiom gluing_estimate ...
opaque RawSheetSum.toIntegralCurrent ...
opaque HasBoundedFlatNorm ... : Prop
axiom gluing_flat_norm_bound ...
opaque HasBoundedCalibrationDefect ... : Prop
axiom calibration_defect_from_gluing ...

-- Calibrated flow and glue cells
opaque calibratedFlow {p : ℕ} (γ : SmoothForm n X (2 * p)) (ψ : CalibratingForm n X (2 * (n - p))) {h : ℝ} (C : Cubulation n X h) : Flow C
opaque glueCells {p : ℕ} {h : ℝ} (C : Cubulation n X h) (int_flow : DirectedEdge C → ℤ) : IntegralCurrent n X (2 * (n - p))
axiom glueCells_isCycle ...
axiom glueCells_mass_bound ...
axiom glueCells_calibration_defect ...
axiom IsValidIntegerApproximation_divergence_free ...
axiom calibratedFlow_divergence_free ...

-- Microstructure sequence
axiom microstructureSequence_defect_bound ...
axiom exists_flow_mass_bound ...
axiom microstructureSequence_flatnorm_bound ...
axiom microstructureSequence_flat_limit_exists ...
```

### Hodge/Kahler/SignedDecomp.lean (1 axiom + errors)

```lean
axiom form_is_bounded_axiom {k : ℕ} (α : SmoothForm n X k) : ∃ M : ℝ, M > 0 ∧ ∀ x, pointwiseComass α x ≤ M

-- ALSO: Fix the 7 tactic errors in signed_decomposition theorem attempt
```

### Hodge/Kahler/Main.lean (3 items)

```lean
axiom integration_represents_fundamental {p : ℕ} (V : AnalyticSubvariety n X) ...
axiom microstructure_limit_represents_class {p : ℕ} (γ : SmoothForm n X (2 * p)) ...
opaque CurrentRepresentsClass {k : ℕ} (T : Current n X (2 * (n - p))) (η : DeRhamCohomologyClass n X (2 * p)) : Prop
```

### Hodge/Utils/BaranyGrinberg.lean (1 item)

```lean
axiom barany_grinberg (v : ι → (Fin d → ℝ)) (hv : ∀ i j, |v i j| ≤ 1) (w : Fin d → ℝ) (hw : ‖w‖ ≤ 1/d) :
    ∃ (f : ι → ℤ), ... -- KEEP AS AXIOM (deep combinatorics)
```

## Deliverables

- [ ] **FIRST: Fix all 7 errors in SignedDecomp.lean**
- [ ] Convert all 24 in `Microstructure.lean`
- [ ] Convert 1 in `SignedDecomp.lean`
- [ ] Convert 3 in `Main.lean`
- [ ] Keep `barany_grinberg` as axiom
- [ ] Total: 29 items (28 to convert)

---

# 📊 Summary

| Agent | Files | Total Items | Must Convert | Can Keep |
|-------|-------|-------------|--------------|----------|
| **1** | Basic, Forms, Norms | 53 | 53 | 0 |
| **2** | Currents, FlatNorm, IntegralCurrents, Calibration | 26 | 26 | 0 |
| **3** | Grassmannian, Cone, TypeDecomp, Manifolds | 32 | 32 | 0 |
| **4** | GAGA, HarveyLawson, Bergman, SheafTheory, Lefschetz, FF, SV | 56 | 48 | 8 |
| **5** | Microstructure, SignedDecomp, Main, BaranyGrinberg + **FIX ERRORS** | 29 | 28 | 1 |
| **TOTAL** | 22 files | **196** | **187** | **9** |

---

# 📋 Agent Prompts

## Agent 1 Prompt

```
You are Agent 1 working on the Hodge Conjecture Lean formalization.

## YOUR FILES
- Hodge/Basic.lean (20 axioms/opaques)
- Hodge/Analytic/Forms.lean (14 axioms/opaques)
- Hodge/Analytic/Norms.lean (19 axioms/opaques)

## YOUR TASK
Convert ALL 53 axioms and opaques to theorems and concrete definitions.

## SPECIFIC ITEMS

### Hodge/Basic.lean
1. opaque IsSmoothAlternating → def using smooth section predicate
2. axiom smoothFormTopologicalSpace_axiom → instance using product topology
3. axioms isSmoothAlternating_zero/add/neg/smul/sub → prove from def
4. opaque smoothExtDeriv → def using Mathlib exterior derivative
5. axioms smoothExtDeriv_extDeriv/add/smul → prove from def
6. axioms instAddCommGroupDeRhamCohomologyClass, instModuleDeRhamCohomologyClass, instModuleRealDeRhamCohomologyClass → prove as instances using Quotient API
7. axiom instHMulDeRhamCohomologyClass → prove wedge product descends to quotient
8. axioms ofForm_add/sub/smul_rat/smul_real → prove using Quotient.liftOn
9. opaque isRationalClass → def using actual rationality condition

### Hodge/Analytic/Forms.lean
1. opaque unitForm → def as constant 1 form
2. opaque wedge → def using exterior algebra wedge
3. opaque hodgeStar → def using Hodge star operator
4. axioms wedge_add/smul/assoc → prove from def
5. axiom smoothExtDeriv_wedge → prove Leibniz rule
6. axioms hodgeStar_add/smul → prove linearity
7. opaque adjointDeriv → def as δ = ±*d*
8. opaque laplacian → def as Δ = dδ + δd
9. axiom laplacian_add → prove linearity
10. opaque lefschetzLambda → def using interior product with ω

### Hodge/Analytic/Norms.lean
1. opaque pointwiseComass → def using sSup { |ω(v)| : ‖v‖ ≤ 1 }
2. axioms pointwiseComass_* → prove from def
3. def comass using iSup of pointwiseComass (already done, but verify)
4. axioms comass_* → prove from def
5. opaque pointwiseInner → def using Hermitian inner product on forms
6. axiom pointwiseInner_self_nonneg → prove from def
7. opaque L2Inner → def as ∫ pointwiseInner dμ
8. axioms L2Inner_add_left/smul_left → prove from def
9. axiom energy_minimizer → prove or mark as deep (Hodge theory)
10. axiom trace_L2_control → prove Sobolev embedding or mark as deep

## RULES
- NO sorry, NO admit
- Do NOT run builds - just write the code
- Use Mathlib wherever possible
- Document non-obvious steps

## OUTPUT FORMAT
Provide complete replacement code for each file section. Use this format:

```lean
-- FILE: Hodge/Basic.lean
-- REPLACING: lines X-Y

<your code here>
```

Provide ALL 53 items.
```

## Agent 2 Prompt

```
You are Agent 2 working on the Hodge Conjecture Lean formalization.

## YOUR FILES
- Hodge/Analytic/Currents.lean (5 axioms/opaques)
- Hodge/Analytic/FlatNorm.lean (9 axioms/opaques)
- Hodge/Analytic/IntegralCurrents.lean (8 axioms/opaques)
- Hodge/Analytic/Calibration.lean (4 axioms/opaques)

## YOUR TASK
Convert ALL 26 axioms and opaques to theorems and concrete definitions.

## SPECIFIC ITEMS

### Hodge/Analytic/Currents.lean
1. opaque mass → def as sSup { |T(ψ)| / comass(ψ) : comass(ψ) > 0 }
2. axiom mass_nonneg → prove sSup of nonneg is nonneg
3. axiom mass_zero → prove 0 current gives 0 mass
4. axiom mass_neg → prove |(-T)(ψ)| = |T(ψ)|
5. axiom mass_add_le → prove triangle inequality

### Hodge/Analytic/FlatNorm.lean
1. opaque flatNorm → def as sInf { mass(S) + mass(R) : T = S + ∂R }
2. axiom flatNorm_nonneg → prove sInf of nonneg
3. axiom flatNorm_zero → prove infimum achieved at S=R=0
4. axiom flatNorm_eq_zero_iff → prove iff T = 0
5. axiom flatNorm_neg → prove -T has same decomposition
6. axiom flatNorm_add_le → prove by combining decompositions
7. axiom flatNorm_le_mass → prove by taking R = 0
8. axiom eval_le_flatNorm → prove |T(ψ)| ≤ |S(ψ)| + |∂R(ψ)| ≤ ...
9. axiom flatNorm_boundary_le → prove ∂(∂R) = 0

### Hodge/Analytic/IntegralCurrents.lean
1. opaque isRectifiable → def using rectifiable sets from Mathlib
2. axiom isRectifiable_empty → prove empty set is rectifiable
3. axiom isRectifiable_union → prove union of rectifiable is rectifiable
4. opaque isIntegral → def as integer multiplicity condition
5. axiom isIntegral_add → prove from def
6. axiom isIntegral_zero_current → prove 0 has multiplicity 0
7. axiom isIntegral_smul → prove c ∈ ℤ preserves integrality
8. axiom isIntegral_boundary → prove boundary of integral is integral

### Hodge/Analytic/Calibration.lean
1. axiom wirtinger_comass_bound → prove ‖ω^p/p!‖ ≤ 1 using Wirtinger inequality
2. axiom calibration_inequality → prove T(ψ) ≤ mass(T) for calibrating ψ
3. axiom spine_theorem → prove or cite Harvey-Lawson decomposition
4. axiom mass_lsc → prove lower semicontinuity of mass in flat topology

## RULES
- NO sorry, NO admit
- Do NOT run builds
- Use Mathlib wherever possible

## OUTPUT FORMAT
```lean
-- FILE: Hodge/Analytic/Currents.lean
-- REPLACING: lines X-Y

<your code here>
```

Provide ALL 26 items.
```

## Agent 3 Prompt

```
You are Agent 3 working on the Hodge Conjecture Lean formalization.

## YOUR FILES
- Hodge/Analytic/Grassmannian.lean (10 axioms/opaques)
- Hodge/Kahler/Cone.lean (4 axioms/opaques)
- Hodge/Kahler/TypeDecomposition.lean (9 axioms/opaques)
- Hodge/Kahler/Manifolds.lean (9 axioms/opaques)

## YOUR TASK
Convert ALL 32 axioms and opaques to theorems and concrete definitions.

## SPECIFIC ITEMS

### Hodge/Analytic/Grassmannian.lean
1. opaque IsVolumeFormOn → def as nonzero top form on subspace
2. axiom IsVolumeFormOn_nonzero → prove from def
3. axiom exists_volume_form_of_submodule_axiom → prove by constructing e₁∧...∧eₚ
4. axiom simpleCalibratedForm_is_smooth → prove smooth dependence on parameters
5. opaque distToCone → def as inf { ‖α - β‖ : β ∈ cone }
6. axiom distToCone_nonneg → prove inf of nonneg
7. opaque coneDefect → def as iSup of distToCone over x
8. axiom coneDefect_nonneg → prove from def
9. axiom radial_minimization → prove by calculus (minimize ‖α - tξ‖²)
10. axiom dist_cone_sq_formula → prove projection formula

### Hodge/Kahler/Cone.lean
1. axiom wirtinger_pairing → prove ⟨ω^p/p!, vol_V⟩ = 1 for complex p-plane V
2. axiom omegaPow_in_interior → prove using wirtinger_pairing + all pairings > 0
3. axiom exists_uniform_interior_radius → prove using compactness + continuity
4. axiom caratheodory_decomposition → prove using Carathéodory's theorem for cones

### Hodge/Kahler/TypeDecomposition.lean
1. opaque isPQForm → def using Dolbeault type decomposition
2. axiom zero_is_pq → prove 0 is (p,q) for all p,q
3. axiom isPQForm_wedge → prove wedge preserves type
4. axiom omega_is_1_1_axiom → prove ω is (1,1) from Kähler definition
5. axiom unitForm_is_0_0 → prove 1 is (0,0)
6. axiom omega_pow_is_p_p_axiom → prove ω^p is (p,p)
7. axiom omega_pow_isClosed → prove dω^p = 0 from dω = 0
8. axiom omega_pow_is_rational → prove from integrality of Kähler class
9. axiom isClosed_omegaPow_scaled → prove scaling preserves closedness

### Hodge/Kahler/Manifolds.lean
1. axiom kahlerMetric_symm → prove Hermitian symmetry
2. axiom isRationalClass_wedge → prove product of rational is rational
3. axiom isRationalClass_smul_rat → prove q • rational is rational
4. axiom omega_isClosed → prove dω = 0 (Kähler condition)
5. axiom omega_is_rational → prove from integral Kähler class
6. axiom isRationalClass_add → prove sum of rational is rational
7. axiom zero_is_rational → prove 0 is rational
8. axiom unitForm_isClosed → prove d(1) = 0
9. axiom unitForm_is_rational → prove 1 is rational

## RULES
- NO sorry, NO admit
- Do NOT run builds

## OUTPUT FORMAT
```lean
-- FILE: Hodge/Analytic/Grassmannian.lean
-- REPLACING: lines X-Y

<your code here>
```

Provide ALL 32 items.
```

## Agent 4 Prompt

```
You are Agent 4 working on the Hodge Conjecture Lean formalization.

## YOUR FILES
- Hodge/Classical/GAGA.lean (18 axioms/opaques)
- Hodge/Classical/HarveyLawson.lean (10 axioms/opaques)
- Hodge/Classical/Bergman.lean (10 axioms/opaques)
- Hodge/Analytic/SheafTheory.lean (10 axioms/opaques)
- Hodge/Classical/Lefschetz.lean (5 axioms/opaques)
- Hodge/Classical/FedererFleming.lean (2 axioms/opaques)
- Hodge/Classical/SerreVanishing.lean (1 axiom)

## YOUR TASK
Convert 48 of 56 items. Keep these 8 as axioms (classical pillars):
- serre_gaga
- harvey_lawson_theorem
- harvey_lawson_represents
- hard_lefschetz_isomorphism
- hard_lefschetz_inverse_form
- tian_convergence
- federer_fleming_compactness
- serre_vanishing

## SPECIFIC ITEMS

### Hodge/Classical/GAGA.lean (18 items, keep serre_gaga)
1. opaque IsAlgebraicSet → def using Zariski closed
2. axioms IsAlgebraicSet_empty/univ/union/inter/isClosed/nontrivial → prove
3. opaque FundamentalClassSet → def as integration current
4. axioms FundamentalClassSet_* → prove
5. axiom exists_hyperplane_algebraic → prove projective has hyperplanes
6. axiom IsAlgebraicSet_isAnalyticSet → prove algebraic ⊂ analytic
7. opaque algebraic_intersection_power → def as iterated intersection
8. axiom algebraic_intersection_power_is_algebraic → prove

### Hodge/Classical/HarveyLawson.lean (10 items, keep hl_theorem/represents)
1. opaque IsAnalyticSet → def using local analytic equations
2. axioms IsAnalyticSet_* → prove closure properties
3. axiom flat_limit_of_cycles_is_cycle → prove ∂ continuous in flat norm

### Hodge/Classical/Bergman.lean (10 items, keep tian_convergence)
1. opaque partial_deriv → def as ∂
2. opaque partial_bar_deriv → def as ∂̄
3. opaque log_h → def as log of metric
4. opaque L2InnerProduct → def as L² pairing
5. opaque log_KM → def
6. opaque SectionsVanishingToOrder → def
7. axiom jet_surjectivity_axiom → prove surjectivity
8. axiom IsHolomorphic_tensor_axiom → prove tensor of holomorphic

### Hodge/Analytic/SheafTheory.lean (10 items)
1. opaque SheafCohomology → def using derived functors (or axiomatize structure)
2. axioms SheafCohomology.inst* → provide instances
3. opaque vanishes → def as H^q = 0
4. axiom vanishes_iff_subsingleton → prove
5. opaque structureSheafAsCoherent → def
6. axiom h0_structure_sheaf_nonvanishing → prove H^0(𝒪) ≠ 0

### Hodge/Classical/Lefschetz.lean (5 items, keep hard_lefschetz_*)
1. axiom lefschetz_on_cohomology → prove L acts on cohomology
2. axiom lefschetz_inverse_cohomology → prove inverse exists
3. axiom lefschetz_compatibility → prove compatibility

### Hodge/Classical/FedererFleming.lean (2 items, keep compactness)
1. axiom deformation_theorem → prove or mark as deep

### Hodge/Classical/SerreVanishing.lean (1 item, keep as axiom)

## RULES
- NO sorry, NO admit
- Do NOT run builds

## OUTPUT FORMAT
```lean
-- FILE: Hodge/Classical/GAGA.lean
-- REPLACING: lines X-Y

<your code here>
```

Provide ALL 48 items to convert.
```

## Agent 5 Prompt

```
You are Agent 5 working on the Hodge Conjecture Lean formalization.

## YOUR FILES
- Hodge/Kahler/Microstructure.lean (24 axioms/opaques)
- Hodge/Kahler/SignedDecomp.lean (1 axiom + 7 BUILD ERRORS)
- Hodge/Kahler/Main.lean (3 axioms/opaques)
- Hodge/Utils/BaranyGrinberg.lean (1 axiom - keep as is)

## CRITICAL: FIX BUILD ERRORS FIRST

The build is currently broken. These errors MUST be fixed before anything else:

```
error: Hodge/Kahler/SignedDecomp.lean:89:28: Tactic `rewrite` failed
error: Hodge/Kahler/SignedDecomp.lean:96:8: Tactic `rewrite` failed  
error: Hodge/Kahler/SignedDecomp.lean:113:57: unsolved goals
error: Hodge/Kahler/SignedDecomp.lean:128:16: Unknown identifier `inv_mul_lt_iff`
error: Hodge/Kahler/SignedDecomp.lean:127:19: unsolved goals
error: Hodge/Kahler/SignedDecomp.lean:136:35: Type mismatch
error: Hodge/Kahler/SignedDecomp.lean:107:19: unsolved goals
```

Fix these errors. Use `sorry` ONLY if absolutely necessary and document why.

## YOUR TASK
After fixing errors, convert 28 of 29 items. Keep `barany_grinberg` as axiom.

## SPECIFIC ITEMS

### Hodge/Kahler/SignedDecomp.lean (fix errors + 1 axiom)
1. FIX ALL 7 ERRORS in the signed_decomposition proof
2. axiom form_is_bounded_axiom → prove using compactness of X

### Hodge/Kahler/Microstructure.lean (24 items)
1. opaque IsComplexSubmanifold → def
2. axiom local_sheet_realization → prove
3. axiom cubulation_exists → prove using standard mesh construction
4. opaque IsValidIntegerApproximation → def
5. axiom IsValidIntegerApproximation_edge_bound → prove
6. axiom integer_transport → prove using Barany-Grinberg
7. opaque IsValidGluing → def
8. axiom gluing_estimate → prove
9. opaque RawSheetSum.toIntegralCurrent → def
10. opaque HasBoundedFlatNorm → def
11. axiom gluing_flat_norm_bound → prove
12. opaque HasBoundedCalibrationDefect → def
13. axiom calibration_defect_from_gluing → prove
14. opaque calibratedFlow → def
15. opaque glueCells → def
16. axiom glueCells_isCycle → prove ∂ = 0
17. axiom glueCells_mass_bound → prove
18. axiom glueCells_calibration_defect → prove
19. axiom IsValidIntegerApproximation_divergence_free → prove
20. axiom calibratedFlow_divergence_free → prove
21. axiom microstructureSequence_defect_bound → prove
22. axiom exists_flow_mass_bound → prove
23. axiom microstructureSequence_flatnorm_bound → prove
24. axiom microstructureSequence_flat_limit_exists → prove using FF compactness

### Hodge/Kahler/Main.lean (3 items)
1. axiom integration_represents_fundamental → prove
2. axiom microstructure_limit_represents_class → prove
3. opaque CurrentRepresentsClass → def

## RULES
- NO sorry, NO admit (except to fix blocking errors, documented)
- Do NOT run builds

## OUTPUT FORMAT
```lean
-- FILE: Hodge/Kahler/SignedDecomp.lean
-- FIX FOR: error at line 89

<your fixed code>
```

Then:
```lean
-- FILE: Hodge/Kahler/Microstructure.lean
-- REPLACING: lines X-Y

<your code here>
```

Fix errors FIRST, then provide ALL 28 items to convert.
```

---

# 📈 Progress Tracker

| Agent | Items | Completed | Remaining |
|-------|-------|-----------|-----------|
| 1 | 53 | 0 | 53 |
| 2 | 26 | 0 | 26 |
| 3 | 32 | 0 | 32 |
| 4 | 56 (48 to convert) | 0 | 48 |
| 5 | 29 (28 to convert) + errors | 0 | 28 + 7 errors |
| **TOTAL** | **196** | **0** | **187 + 7 errors** |
