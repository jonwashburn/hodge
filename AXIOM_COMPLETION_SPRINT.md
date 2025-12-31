# Hodge Conjecture Lean Formalization: Full Sprint Plan

**Generated:** 2024-12-30  
**Last Update:** 2024-12-31  
**Build Status:** ✅ **BUILD PASSES** — All Hodge modules compile!  
**Total Axioms/Opaques:** 211  
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
| **🔴 NO BUILDS 🔴** | **AGENTS DO NOT RUN `lake build`!** Only the coordinator runs builds. |
| **Mathlib first** | Search before writing custom lemmas |
| **Document everything** | Every non-obvious step needs a comment |

### ⚠️ CRITICAL: Build Policy

```
┌─────────────────────────────────────────────────────────────────┐
│  AGENTS: DO NOT RUN `lake build`, `lake exe`, or any build     │
│  commands. Write your code and submit. The COORDINATOR will    │
│  run the build, collect errors, and reassign as needed.        │
│                                                                 │
│  WHY: Builds take 10-30 minutes. Running them in parallel      │
│  wastes resources and causes conflicts.                        │
└─────────────────────────────────────────────────────────────────┘
```

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

## 📊 AXIOM DISTRIBUTION BY FILE (Current Count: 211)

| File | Axioms/Opaques | Assigned To |
|------|----------------|-------------|
| `Hodge/Analytic/Forms.lean` | 31 | **Agent 1** |
| `Hodge/Basic.lean` | 28 | **Agent 1** |
| `Hodge/Analytic/Norms.lean` | 23 | **Agent 1** |
| `Hodge/Analytic/Currents.lean` | 16 | **Agent 2** |
| `Hodge/Analytic/IntegralCurrents.lean` | 12 | **Agent 2** |
| `Hodge/Analytic/FlatNorm.lean` | 11 | **Agent 2** |
| `Hodge/Analytic/Grassmannian.lean` | 11 | **Agent 3** |
| `Hodge/Kahler/TypeDecomposition.lean` | 10 | **Agent 3** |
| `Hodge/Classical/HarveyLawson.lean` | 10 | **Agent 4** |
| `Hodge/Classical/GAGA.lean` | 10 | **Agent 4** |
| `Hodge/Kahler/Microstructure.lean` | 8 | **Agent 5** |
| `Hodge/Kahler/Manifolds.lean` | 7 | **Agent 3** |
| `Hodge/Classical/Lefschetz.lean` | 7 | **Agent 4** |
| `Hodge/Analytic/SheafTheory.lean` | 5 | **Agent 4** |
| `Hodge/Analytic/Calibration.lean` | 5 | **Agent 2** |
| `Hodge/Kahler/Cone.lean` | 4 | **Agent 3** |
| `Hodge/Classical/Bergman.lean` | 4 | **Agent 4** |
| `Hodge/Kahler/Main.lean` | 3 | **Agent 5** |
| `Hodge/Kahler/SignedDecomp.lean` | 2 | **Agent 5** |
| `Hodge/Classical/FedererFleming.lean` | 2 | **Agent 4** |
| `Hodge/Utils/BaranyGrinberg.lean` | 1 | **Agent 5** (keep as axiom) |
| `Hodge/Classical/SerreVanishing.lean` | 1 | **Agent 4** (keep as axiom) |

---

## 🔧 BUILD STATUS: ✅ ALL PASSING

### 🎉 The entire Hodge library now compiles!

All errors have been resolved. The codebase uses a consistent axiom/opaque approach.

**Next Goal:** Convert 211 axioms/opaques → theorems/defs (keeping ~12 classical pillars).

### Agent Workload Summary

| Agent | Files | Items | LOC Est |
|-------|-------|-------|---------|
| **Agent 1** | Basic, Forms, Norms | **82** | ~2000 |
| **Agent 2** | Currents, FlatNorm, IntegralCurrents, Calibration | **44** | ~1100 |
| **Agent 3** | Grassmannian, Cone, TypeDecomp, Manifolds | **32** | ~800 |
| **Agent 4** | GAGA, HarveyLawson, Bergman, SheafTheory, Lefschetz, FF, SV | **39** | ~1000 |
| **Agent 5** | Microstructure, SignedDecomp, Main, BaranyGrinberg | **14** | ~400 |
| **TOTAL** | 22 files | **211** | ~5300 |

---

# 🤖 AGENT 1: Forms & Norms Infrastructure

## Ownership

| File | Axioms/Opaques |
|------|----------------|
| `Hodge/Basic.lean` | 28 |
| `Hodge/Analytic/Forms.lean` | 31 |
| `Hodge/Analytic/Norms.lean` | 23 |
| **TOTAL** | **82** |

## Full Axiom List

### Hodge/Basic.lean (28 items)

```lean
-- Line 32: prove existence
axiom exists_not_isClosed_set (X : Type*) [TopologicalSpace X] [Nonempty X] : ∃ S : Set X, ¬ IsClosed S

-- Line 35: Convert to def using exterior algebra
opaque SmoothForm (n : ℕ) (X : Type u) (k : ℕ)

-- Lines 39-61: Prove as instances
axiom SmoothForm.zero (n : ℕ) (X : Type u) (k : ℕ) : SmoothForm n X k
axiom SmoothForm.instAddCommGroup (n : ℕ) (X : Type u) (k : ℕ) : AddCommGroup (SmoothForm n X k)
axiom SmoothForm.instModuleComplex (n : ℕ) (X : Type u) (k : ℕ) : Module ℂ (SmoothForm n X k)
axiom SmoothForm.instModuleReal (n : ℕ) (X : Type u) (k : ℕ) : Module ℝ (SmoothForm n X k)
axiom SmoothForm.instTopologicalSpace (n : ℕ) (X : Type u) (k : ℕ) : TopologicalSpace (SmoothForm n X k)

-- Line 70: Convert to def
opaque as_alternating : SmoothForm n X k → (x : X) → (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ

-- Lines 75-86: Convert/prove exterior derivative
opaque smoothExtDeriv {n : ℕ} {X : Type u} ... (ω : SmoothForm n X k) : SmoothForm n X (k + 1)
axiom smoothExtDeriv_add ... : smoothExtDeriv (ω + η) = smoothExtDeriv ω + smoothExtDeriv η
axiom smoothExtDeriv_smul ... : smoothExtDeriv (c • ω) = c • smoothExtDeriv ω

-- Line 149: Prove
axiom isFormClosed_smul_real ... : IsFormClosed ω → IsFormClosed (r • ω)

-- Lines 228-250: Prove as instances using Quotient API
axiom instAddCommGroupDeRhamCohomologyClass : AddCommGroup (DeRhamCohomologyClass n X k)
axiom instModuleDeRhamCohomologyClass : Module ℂ (DeRhamCohomologyClass n X k)
axiom smulRat_DeRhamCohomologyClass : HSMul ℚ (DeRhamCohomologyClass n X k) (DeRhamCohomologyClass n X k)
axiom neg_eq_neg_one_smul_rat_DeRham (η) : -η = (-1 : ℚ) • η
axiom instHMulDeRhamCohomologyClass : HMul (DeRhamCohomologyClass n X k) (DeRhamCohomologyClass n X l) (DeRhamCohomologyClass n X (k + l))

-- Lines 263-289: Prove from Quotient.liftOn
axiom ofForm_add (ω η) (hω hη) : ofForm (ω + η) _ = ofForm ω hω + ofForm η hη
axiom ofForm_smul (c) (ω) (hω) : ofForm (c • ω) _ = c • ofForm ω hω
axiom ofForm_neg (ω) (hω) : ofForm (-ω) _ = -ofForm ω hω
axiom ofForm_smul_real (r) (ω) (hω) : ofForm (r • ω) _ = r • ofForm ω hω

-- Lines 306-349: Rationality predicates
opaque isRationalClass {n : ℕ} {X : Type u} {k : ℕ} ... (η : DeRhamCohomologyClass n X k) : Prop
axiom isRationalClass_zero : isRationalClass (0 : DeRhamCohomologyClass n X k)
axiom isRationalClass_add (η₁ η₂) : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂)
axiom isRationalClass_smul_rat (q : ℚ) (η) : isRationalClass η → isRationalClass (q • η)
axiom isRationalClass_mul (η₁ η₂) : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂)

-- Lines 357-360: (p,p) form type
opaque isPPForm' (n : ℕ) (X : Type u) ... (p : ℕ) (ω : SmoothForm n X (2 * p)) : Prop
axiom isPPForm_zero : isPPForm' n X p (0 : SmoothForm n X (2 * p))
```

### Hodge/Analytic/Forms.lean (31 items)

```lean
-- Line 30: Wedge product
opaque smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) : SmoothForm n X (k + l)

-- Lines 37-69: Wedge properties
axiom isFormClosed_wedge {k l : ℕ} (ω η) : IsFormClosed ω → IsFormClosed η → IsFormClosed (smoothWedge ω η)
axiom smoothWedge_add_right {k l : ℕ} (ω η₁ η₂) : smoothWedge ω (η₁ + η₂) = smoothWedge ω η₁ + smoothWedge ω η₂
axiom smoothWedge_add_left {k l : ℕ} (ω₁ ω₂ η) : smoothWedge (ω₁ + ω₂) η = smoothWedge ω₁ η + smoothWedge ω₂ η
axiom smoothWedge_smul_right {k l : ℕ} (c ω η) : smoothWedge ω (c • η) = c • smoothWedge ω η
axiom smoothWedge_smul_left {k l : ℕ} (c ω η) : smoothWedge (c • ω) η = c • smoothWedge ω η
axiom smoothWedge_assoc {k l m : ℕ} (α β γ) : smoothWedge (smoothWedge α β) γ = smoothWedge α (smoothWedge β γ)
axiom smoothWedge_zero_right {k l : ℕ} (ω) : smoothWedge ω 0 = 0
axiom smoothWedge_zero_left {k l : ℕ} (η) : smoothWedge 0 η = 0
axiom smoothWedge_comm {k l : ℕ} (α β) : smoothWedge α β = (-1)^(k*l) • smoothWedge β α

-- Lines 85-94: Exterior derivative
axiom smoothExtDeriv_extDeriv {k : ℕ} (ω) : ...
axiom smoothExtDeriv_smul_real {k : ℕ} (r ω) : smoothExtDeriv (r • ω) = r • smoothExtDeriv ω
axiom smoothExtDeriv_wedge {k l : ℕ} (α β) : smoothExtDeriv (smoothWedge α β) = ...

-- Lines 103-110: Unit form & Hodge star
opaque unitForm : SmoothForm n X 0
opaque hodgeStar {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (2 * n - k)

-- Lines 115-129: Hodge star properties
axiom hodgeStar_add {k : ℕ} (α β) : hodgeStar (α + β) = hodgeStar α + hodgeStar β
axiom hodgeStar_smul_real {k : ℕ} (r α) : hodgeStar (r • α) = r • hodgeStar α
axiom hodgeStar_hodgeStar {k : ℕ} (α) : hodgeStar (hodgeStar α) = (-1)^(k*(2*n-k)) • α

-- Lines 135-154: Adjoint derivative
opaque adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1)
axiom adjointDeriv_add {k : ℕ} (α β) : adjointDeriv (α + β) = adjointDeriv α + adjointDeriv β
axiom adjointDeriv_smul_real {k : ℕ} (r α) : adjointDeriv (r • α) = r • adjointDeriv α
axiom adjointDeriv_squared {k : ℕ} (α) : adjointDeriv (adjointDeriv α) = 0

-- Lines 163-192: Laplacian
opaque laplacian {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k
axiom laplacian_add {k : ℕ} (α β) : laplacian (α + β) = laplacian α + laplacian β
axiom laplacian_smul_real {k : ℕ} (r α) : laplacian (r • α) = r • laplacian α
axiom isHarmonic_implies_closed {k : ℕ} (ω) : laplacian ω = 0 → smoothExtDeriv ω = 0
axiom isHarmonic_implies_coclosed {k : ℕ} (ω) : laplacian ω = 0 → adjointDeriv ω = 0

-- Lines 203-216: Lefschetz operators
opaque lefschetzLambda {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k - 2)
axiom lefschetzL_add {k : ℕ} [K : KahlerManifold n X] (α β) : lefschetzL (α + β) = lefschetzL α + lefschetzL β
axiom lefschetzLambda_add {k : ℕ} (α β) : lefschetzLambda (α + β) = lefschetzLambda α + lefschetzLambda β
axiom lefschetz_commutator {k : ℕ} (α) : ...
```

### Hodge/Analytic/Norms.lean (23 items)

```lean
-- Line 26: Convert to def using sSup
opaque pointwiseComass {n : ℕ} {X : Type*} ... (α : SmoothForm n X k) (x : X) : ℝ

-- Lines 31-62: Prove from definition
axiom pointwiseComass_nonneg ... : pointwiseComass α x ≥ 0
axiom pointwiseComass_zero ... : pointwiseComass 0 x = 0
axiom pointwiseComass_add_le ... : pointwiseComass (α + β) x ≤ pointwiseComass α x + pointwiseComass β x
axiom pointwiseComass_smul ... : pointwiseComass (c • α) x = |c| * pointwiseComass α x
axiom SmoothForm.neg_eq_neg_one_smul ... : -α = (-1 : ℝ) • α
axiom pointwiseComass_continuous ... : Continuous (pointwiseComass α)

-- Lines 106-144: Comass properties
axiom comass_add_le ... : comass (α + β) ≤ comass α + comass β
axiom comass_smul ... : comass (c • α) = |c| * comass α
axiom comass_eq_zero_iff ... : comass α = 0 ↔ α = 0

-- Lines 153-190: Inner products
opaque pointwiseInner {n : ℕ} {X : Type*} ... (α β : SmoothForm n X k) (x : X) : ℝ
axiom pointwiseInner_self_nonneg ... : pointwiseInner α α x ≥ 0
opaque L2Inner {n : ℕ} {X : Type*} ... (α β : SmoothForm n X k) : ℝ
axiom L2Inner_add_left ... : L2Inner (α + β) γ = L2Inner α γ + L2Inner β γ
axiom L2Inner_smul_left ... : L2Inner (c • α) β = c * L2Inner α β
axiom L2Inner_self_nonneg ... : L2Inner α α ≥ 0

-- Lines 212-307: Deep theorems
axiom energy_minimizer ... : harmonic representative minimizes energy
axiom trace_L2_control ... : ∃ C > 0, comass α ≤ C * L2NormForm α
axiom pointwiseInner_comm ... : pointwiseInner α β = pointwiseInner β α
axiom L2Inner_comm ... : L2Inner α β = L2Inner β α
axiom L2Inner_cauchy_schwarz ... : |L2Inner α β| ≤ L2NormForm α * L2NormForm β
axiom L2NormForm_add_le ... : L2NormForm (α + β) ≤ L2NormForm α + L2NormForm β
axiom L2NormForm_smul ... : L2NormForm (c • α) = |c| * L2NormForm α
```

## Deliverables

- [ ] Convert all 28 `opaque`/`axiom` in `Basic.lean` to `def`/`theorem`
- [ ] Convert all 31 in `Forms.lean`
- [ ] Convert all 23 in `Norms.lean`
- [ ] **Total: 82 items**
- [ ] Provide complete, compilable code for each

## Key Mathlib References

```
Mathlib.Analysis.Normed.Group.Basic
Mathlib.Analysis.NormedSpace.Basic
Mathlib.Topology.ContinuousFunction.Compact
Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
Mathlib.Analysis.InnerProductSpace.Basic
Mathlib.Geometry.Manifold.MFDeriv.Basic
```

---

# 🤖 AGENT 2: Currents & GMT

## Ownership

| File | Axioms/Opaques |
|------|----------------|
| `Hodge/Analytic/Currents.lean` | 16 |
| `Hodge/Analytic/FlatNorm.lean` | 11 |
| `Hodge/Analytic/IntegralCurrents.lean` | 12 |
| `Hodge/Analytic/Calibration.lean` | 5 |
| **TOTAL** | **44** |

## Full Axiom List

### Hodge/Analytic/Currents.lean (16 items)

```lean
-- Lines 36-55: Current linearity
axiom map_add' ... : T.toFun (ω + η) = T.toFun ω + T.toFun η
axiom map_smul' ... : T.toFun (c • ω) = c * T.toFun ω
axiom zero (n k) : Current n X k  -- zero current

-- Lines 64-76: Current operations
opaque add_curr (T₁ T₂ : Current n X k) : Current n X k
opaque neg_curr (T : Current n X k) : Current n X k
opaque smul_curr (r : ℝ) (T : Current n X k) : Current n X k

-- Lines 85-94: Mass
opaque mass (T : Current n X k) : ℝ
axiom mass_nonneg (T) : mass T ≥ 0
axiom mass_zero : mass (0 : Current n X k) = 0
axiom mass_neg (T) : mass (-T) = mass T
axiom mass_add_le (S T) : mass (S + T) ≤ mass S + mass T
axiom mass_smul (r T) : mass (r • T) = |r| * mass T
axiom is_bounded (T) : ∃ M, ∀ ω, |T.toFun ω| ≤ M * comass ω
axiom zero_toFun (ω) : (0 : Current n X k).toFun ω = 0

-- Lines 101-107: Boundary
opaque boundary (T : Current n X (k + 1)) : Current n X k
axiom boundary_boundary (T) : boundary (boundary T) = 0
```

### Hodge/Analytic/FlatNorm.lean (11 items)

```lean
-- Line 26: Flat norm
opaque flatNorm {k : ℕ} (T : Current n X k) : ℝ

-- Lines 29-61: Flat norm properties
axiom flatNorm_nonneg (T) : flatNorm T ≥ 0
axiom flatNorm_zero : flatNorm (0 : Current n X k) = 0
axiom eval_le_mass (T ψ) : |T.toFun ψ| ≤ comass ψ * mass T
axiom eval_le_flatNorm (T ψ) : |T.toFun ψ| ≤ comass ψ * flatNorm T
axiom flatNorm_le_mass (T) : flatNorm T ≤ mass T
axiom flatNorm_add_le (S T) : flatNorm (S + T) ≤ flatNorm S + flatNorm T
axiom flatNorm_neg (T) : flatNorm (-T) = flatNorm T
axiom flatNorm_eq_zero_iff (T) : flatNorm T = 0 ↔ T = 0
axiom flatNorm_smul (c T) : flatNorm (c • T) = |c| * flatNorm T
axiom flatNorm_boundary_le (T) : flatNorm (boundary T) ≤ flatNorm T
```

### Hodge/Analytic/IntegralCurrents.lean (12 items)

```lean
-- Lines 27-30: Rectifiability
opaque isRectifiable (k : ℕ) (S : Set X) : Prop
axiom isRectifiable_empty (k) : isRectifiable k (∅ : Set X)
axiom isRectifiable_union (k S₁ S₂) : isRectifiable k S₁ → isRectifiable k S₂ → isRectifiable k (S₁ ∪ S₂)

-- Lines 36-45: Polyhedral chains
opaque IntegralPolyhedralChain (n : ℕ) (X : Type*) (k : ℕ) : Set (Current n X k)
axiom polyhedral_add (S T) : S ∈ IntegralPolyhedralChain → T ∈ IntegralPolyhedralChain → (S + T) ∈ IntegralPolyhedralChain
axiom polyhedral_zero : (0 : Current n X k) ∈ IntegralPolyhedralChain n X k
axiom polyhedral_smul (c : ℤ) (T) : T ∈ IntegralPolyhedralChain → (c • T) ∈ IntegralPolyhedralChain
axiom polyhedral_boundary (T) : T ∈ IntegralPolyhedralChain → boundary T ∈ IntegralPolyhedralChain

-- Lines 55-66: Integrality
axiom isIntegral_add (S T) : isIntegral S → isIntegral T → isIntegral (S + T)
axiom isIntegral_zero_current (k) : isIntegral (0 : Current n X k)
axiom isIntegral_smul (c : ℤ) (T) : isIntegral T → isIntegral (c • T)
axiom isIntegral_boundary (T) : isIntegral T → isIntegral (boundary T)
```

### Hodge/Analytic/Calibration.lean (5 items)

```lean
-- Line 35: Wirtinger inequality
axiom wirtinger_comass_bound (p) : comass (omegaPow n X p) ≤ 1

-- Lines 54-84: Calibration
axiom calibration_inequality (T ψ) : T.toFun ψ.form ≤ mass T
axiom spine_theorem (T S G ψ) : ...
axiom mass_lsc (T : ℕ → Current) (T_limit) : mass T_limit ≤ liminf (mass ∘ T)

-- Line 92: Limit calibration (⚠️ STRATEGY-CRITICAL)
axiom limit_is_calibrated (T : ℕ → Current) (T_limit) (ψ) : ... → is_calibrated T_limit ψ
```

## Deliverables

- [ ] Convert all 16 in `Currents.lean`
- [ ] Convert all 11 in `FlatNorm.lean`
- [ ] Convert all 12 in `IntegralCurrents.lean`
- [ ] Convert all 5 in `Calibration.lean`
- [ ] **Total: 44 items**

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

# 🤖 AGENT 3: Grassmannian & Kähler Geometry

## Ownership

| File | Axioms/Opaques |
|------|----------------|
| `Hodge/Analytic/Grassmannian.lean` | 11 |
| `Hodge/Kahler/Cone.lean` | 4 |
| `Hodge/Kahler/TypeDecomposition.lean` | 10 |
| `Hodge/Kahler/Manifolds.lean` | 7 |
| **TOTAL** | **32** |

## Full Axiom List

### Hodge/Analytic/Grassmannian.lean (11 items)

```lean
-- Lines 43-51: Volume forms
opaque IsVolumeFormOn {n : ℕ} {X : Type*} ... (x : X) (p : ℕ) (V : Submodule ℂ ...) (ω : ...) : Prop
axiom IsVolumeFormOn_nonzero ... : IsVolumeFormOn x p V ω → ω ≠ 0

-- Lines 69-97: Existence and calibration
axiom exists_volume_form_of_submodule_axiom (p x V) (hV : finrank V = p) : ∃ ω, IsVolumeFormOn x p V ω
axiom simpleCalibratedForm (p x V) : ...

-- Lines 121-152: Cone geometry
axiom calibratedCone_hull_pointed (p x) : pointed (calibratedCone p x)
opaque distToCone (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) : ℝ
axiom distToCone_nonneg (p α x) : distToCone p α x ≥ 0
opaque coneDefect (p : ℕ) (α : SmoothForm n X (2 * p)) : ℝ
axiom coneDefect_nonneg (p α) : coneDefect p α ≥ 0
axiom radial_minimization (x ξ α) : ∃ t_opt, ...
axiom dist_cone_sq_formula (p α x) : (distToCone p α x)^2 = ...
```

### Hodge/Kahler/Cone.lean (4 items)

```lean
-- Lines 65-105: Wirtinger and cone structure
axiom wirtinger_pairing (p x ξ) (hξ) : pointwiseInner (omegaPow_point p x) ξ x = 1
axiom omegaPow_in_interior (p x) : omegaPow_point p x ∈ interior (stronglyPositiveCone p x)
axiom exists_uniform_interior_radius (p) [CompactSpace X] [Nonempty X] :
    ∃ r > 0, ∀ x, Metric.ball (omegaPow_point p x) r ⊆ stronglyPositiveCone p x
axiom caratheodory_decomposition (p x α) (hα : α ∈ stronglyPositiveCone p x) :
    ∃ (ξ : Fin (n.choose p + 1) → SmoothForm n X (2 * p)) (c : Fin (n.choose p + 1) → ℝ), ...
```

### Hodge/Kahler/TypeDecomposition.lean (10 items)

```lean
-- Line 56: (p,q)-form predicate
opaque isPQForm (n X p q) (ω : SmoothForm n X (p + q)) : Prop

-- Lines 69-132: Type decomposition properties
axiom zero_is_pq (n X p q) : isPQForm n X p q 0
axiom isPQForm_wedge ... : isPQForm n X p q α → isPQForm n X r s β → isPQForm n X (p+r) (q+s) (smoothWedge α β)
axiom omega_is_1_1_axiom : isPQForm n X 1 1 K.omega_form
opaque kahlerPow (p : ℕ) : SmoothForm n X (2 * p)
axiom unitForm_is_0_0 : isPPFormTD n X 0 unitForm
axiom omega_pow_is_p_p_axiom (p) : isPPFormTD n X p (kahlerPow p)
axiom omega_pow_IsFormClosed (p) : IsFormClosed (kahlerPow p)
axiom omega_pow_is_rational (p) : isRationalClass ⟦kahlerPow p, omega_pow_IsFormClosed p⟧
axiom IsFormClosed_omegaPow_scaled (p) : IsFormClosed ((1 / (p.factorial : ℝ)) • kahlerPow p)
```

### Hodge/Kahler/Manifolds.lean (7 items)

```lean
-- Lines 26-54: Kähler manifold axioms
axiom kahlerMetric_symm (x v w) : K.kahlerMetric x v w = conj (K.kahlerMetric x w v)
axiom isRationalClass_wedge ... : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂)
axiom omega_isClosed : IsFormClosed K.omega_form
axiom omega_is_rational : isRationalClass ⟦K.omega_form, omega_isClosed⟧
axiom zero_is_rational {k} : isRationalClass (0 : DeRhamCohomologyClass n X k)
axiom unitForm_isClosed : IsFormClosed (unitForm : SmoothForm n X 0)
axiom unitForm_is_rational : isRationalClass ⟦unitForm, unitForm_isClosed⟧
```

## Deliverables

- [ ] Convert all 11 in `Grassmannian.lean`
- [ ] Convert all 4 in `Cone.lean`
- [ ] Convert all 10 in `TypeDecomposition.lean`
- [ ] Convert all 7 in `Manifolds.lean`
- [ ] **Total: 32 items**

---

# 🤖 AGENT 4: Classical Theorems

## Ownership

| File | Axioms/Opaques |
|------|----------------|
| `Hodge/Classical/GAGA.lean` | 10 |
| `Hodge/Classical/HarveyLawson.lean` | 10 |
| `Hodge/Classical/Lefschetz.lean` | 7 |
| `Hodge/Analytic/SheafTheory.lean` | 5 |
| `Hodge/Classical/Bergman.lean` | 4 |
| `Hodge/Classical/FedererFleming.lean` | 2 |
| `Hodge/Classical/SerreVanishing.lean` | 1 |
| **TOTAL** | **39** |

## Full Axiom List

### Hodge/Classical/GAGA.lean (10 items)

```lean
-- Line 20: Zariski closed predicate
opaque IsZariskiClosed {n : ℕ} (X : Type u) ... (Z : Set X) : Prop

-- Lines 48-81: Algebraic set properties
axiom IsAlgebraicSet_empty (n X) : IsAlgebraicSet (∅ : Set X)
axiom IsAlgebraicSet_univ (n X) : IsAlgebraicSet (Set.univ : Set X)
axiom IsAlgebraicSet_union (n X Z₁ Z₂) : IsAlgebraicSet Z₁ → IsAlgebraicSet Z₂ → IsAlgebraicSet (Z₁ ∪ Z₂)
axiom IsAlgebraicSet_intersection (n X Z₁ Z₂) : IsAlgebraicSet Z₁ → IsAlgebraicSet Z₂ → IsAlgebraicSet (Z₁ ∩ Z₂)
axiom IsAlgebraicSet_isClosed (n X Z) : IsAlgebraicSet Z → IsClosed Z
axiom IsAlgebraicSet_isAnalyticSet (n X Z) : IsAlgebraicSet Z → IsAnalyticSet Z

-- Line 93: GAGA bridge (⚠️ KEEP AS AXIOM - classical pillar)
axiom serre_gaga {p} (V : AnalyticSubvariety n X) (hV_codim : V.codim = p) : ∃ W : AlgebraicSubvariety n X, ...

-- Lines 167-172: Fundamental class
axiom FundamentalClassSet_additive (p Z₁ Z₂) (h_disjoint) : FundamentalClassSet p (Z₁ ∪ Z₂) = ...
axiom FundamentalClassSet_rational (p Z) (h : isAlgebraicSubvariety n X Z) : isRationalClass ⟦FundamentalClassSet p Z, ...⟧
```

### Hodge/Classical/HarveyLawson.lean (10 items)

```lean
-- Line 24: Analytic set predicate
opaque IsAnalyticSet {n : ℕ} {X : Type*} ... (S : Set X) : Prop

-- Lines 29-65: Analytic set properties
axiom IsAnalyticSet_empty : IsAnalyticSet (∅ : Set X)
axiom IsAnalyticSet_univ : IsAnalyticSet (Set.univ : Set X)
axiom IsAnalyticSet_union (S₁ S₂) : IsAnalyticSet S₁ → IsAnalyticSet S₂ → IsAnalyticSet (S₁ ∪ S₂)
axiom IsAnalyticSet_inter (S₁ S₂) : IsAnalyticSet S₁ → IsAnalyticSet S₂ → IsAnalyticSet (S₁ ∩ S₂)
axiom IsAnalyticSet_isClosed (S) : IsAnalyticSet S → IsClosed S
axiom IsAnalyticSet_nontrivial : ∃ S, IsAnalyticSet S ∧ S ≠ ∅ ∧ S ≠ Set.univ

-- Lines 110-118: Harvey-Lawson (⚠️ KEEP AS AXIOM - classical pillar)
axiom harvey_lawson_theorem (hyp : HarveyLawsonHypothesis n X k) : ∃ V : AnalyticSubvariety n X, ...
axiom harvey_lawson_represents (hyp : HarveyLawsonHypothesis n X k) : ...
axiom flat_limit_of_cycles_is_cycle ... -- ⚠️ STRATEGY-CRITICAL: boundary continuous in flat norm
```

### Hodge/Classical/Lefschetz.lean (7 items)

```lean
-- Line 19: Wedge product on cohomology
axiom ofForm_wedge_add (n X k l ω η ω' η') : ...

-- Lines 27-61: Lefschetz operator
opaque lefschetz_operator (n X k) : DeRhamCohomologyClass n X k → DeRhamCohomologyClass n X (k + 2)
axiom lefschetz_operator_eval (n X k η) : lefschetz_operator n X k η = η * ⟦K.omega_form, ...⟧
axiom hard_lefschetz_bijective (n X p') : Function.Bijective (lefschetz_operator^(n - 2*p'))
opaque lefschetz_inverse_cohomology (n X k) : DeRhamCohomologyClass n X k → DeRhamCohomologyClass n X (k - 2)

-- Lines 83-91: Hard Lefschetz (⚠️ KEEP AS AXIOMS - classical pillar)
axiom hard_lefschetz_isomorphism {p'} (h_range : p' ≤ n / 2) : ...
axiom hard_lefschetz_inverse_form {p} (hp : p > n / 2) : ...
```

### Hodge/Analytic/SheafTheory.lean (5 items)

```lean
-- Line 58: Finite dimensionality
axiom SheafCohomology.finiteDimensional' (F q) : FiniteDimensional ℂ (SheafCohomology F q)

-- Lines 89-121: Structure sheaf
axiom structureSheafAsCoherent (n X) : CoherentSheaf n X
axiom h0_structure_sheaf_nonvanishing : ¬ vanishes (structureSheafAsCoherent n X) 0
axiom structureSheaf_exists (n X) : ∃ F : CoherentSheaf n X, ...
axiom idealSheaf_exists (Z) : ∃ I : CoherentSheaf n X, ...
```

### Hodge/Classical/Bergman.lean (4 items)

```lean
-- Lines 101-119: Holomorphic sections
axiom IsHolomorphic_add (L s₁ s₂) : IsHolomorphic s₁ → IsHolomorphic s₂ → IsHolomorphic (s₁ + s₂)
axiom IsHolomorphic_smul (L c s) : IsHolomorphic s → IsHolomorphic (c • s)

-- Lines 189-218: Bergman/Tian (⚠️ KEEP AS AXIOM - classical pillar)
axiom tian_convergence (L : HolomorphicLineBundle n X) [IsAmple L] : ...
axiom jet_surjectivity (L x k) [IsAmple L] : ...
```

### Hodge/Classical/FedererFleming.lean (2 items)

```lean
-- Line 30: Deformation theorem
axiom deformation_theorem (k T ε) (hε : ε > 0) : ∃ P S, ...

-- Line 59: Federer-Fleming (⚠️ KEEP AS AXIOM - classical pillar)
axiom federer_fleming_compactness (k) : ...
```

### Hodge/Classical/SerreVanishing.lean (1 item)

```lean
-- Line 31: Serre vanishing (⚠️ KEEP AS AXIOM - classical pillar)
axiom serre_vanishing (L : HolomorphicLineBundle n X) [IsAmple L] : ...
```

## Deliverables

- [ ] Convert 10 in `GAGA.lean` (keeping `serre_gaga` as axiom)
- [ ] Convert 10 in `HarveyLawson.lean` (keeping `harvey_lawson_theorem/represents` as axioms)
- [ ] Convert 7 in `Lefschetz.lean` (keeping `hard_lefschetz_*` as axioms)
- [ ] Convert 5 in `SheafTheory.lean`
- [ ] Convert 4 in `Bergman.lean` (keeping `tian_convergence` as axiom)
- [ ] Convert 2 in `FedererFleming.lean` (keeping `federer_fleming_compactness` as axiom)
- [ ] Keep 1 in `SerreVanishing.lean` as axiom
- [ ] **Total: 39 items (minus ~8 classical pillars = 31 to convert)**

---

# 🤖 AGENT 5: Microstructure & Main Proof

## Ownership

| File | Axioms/Opaques |
|------|----------------|
| `Hodge/Kahler/Microstructure.lean` | 8 |
| `Hodge/Kahler/SignedDecomp.lean` | 2 |
| `Hodge/Kahler/Main.lean` | 3 |
| `Hodge/Utils/BaranyGrinberg.lean` | 1 (keep as axiom) |
| **TOTAL** | **14** |

## Full Axiom List

### Hodge/Kahler/Microstructure.lean (8 items)

```lean
-- Line 41: Local realization
axiom local_sheet_realization (p x ξ) (hξ : ξ ∈ simpleCalibratedForms p x) :
    ∃ Y, IsComplexSubmanifold Y p ∧ x ∈ Y ∧ tangent_to_ξ Y x ξ

-- Line 90: Integer transport (uses Barany-Grinberg)
axiom integer_transport (p C target) : ∃ int_flow, IsValidIntegerApproximation ...

-- Lines 105-108: Pairing and current conversion
opaque SmoothForm.pairing {p} (α : SmoothForm n X (2*p)) (β : SmoothForm n X (2*(n-p))) : ℝ
opaque RawSheetSum.toIntegralCurrent {p hscale} ... : IntegralCurrent n X (2 * (n - p))

-- Lines 120-160: Gluing estimates
axiom gluing_estimate (p h C) ... : flat_norm_bound ∧ calibration_defect_bound
axiom cubulation_exists (h) (hh : h > 0) : Cubulation n X h
axiom gluing_flat_norm_bound (p h hh C) : ...
axiom calibration_defect_from_gluing (p h hh C) : ...
```

### Hodge/Kahler/SignedDecomp.lean (2 items)

```lean
-- Line 27: Boundedness (prove using compactness)
axiom form_is_bounded {k} (α : SmoothForm n X k) : ∃ M > 0, ∀ x, pointwiseComass α x ≤ M

-- Line 58: Signed decomposition (⚠️ STRATEGY-CRITICAL)
axiom signed_decomposition {p} (γ : SmoothForm n X (2*p)) (h_closed : IsFormClosed γ) (h_rational : isRationalClass ⟦γ, h_closed⟧) :
    ∃ (γ₊ γ₋ : SmoothForm n X (2*p)), γ = γ₊ - γ₋ ∧ γ₊ ∈ stronglyPositiveCone p ∧ γ₋ ∈ stronglyPositiveCone p
```

### Hodge/Kahler/Main.lean (3 items)

```lean
-- Line 94: Harvey-Lawson produces fundamental class (⚠️ STRATEGY-CRITICAL)
axiom harvey_lawson_fundamental_class {p} (T_limit : IntegralCurrent n X (2*(n-p))) (η : DeRhamCohomologyClass n X (2*p))
    (h_hl : HarveyLawsonHypothesis_satisfied T_limit) : ∃ V : AlgebraicSubvariety n X, ...

-- Line 143: ωᵖ represents multiple
axiom omega_pow_represents_multiple {p} (c : ℚ) (hc : c > 0) : ...

-- Line 150: Lefschetz lift (⚠️ STRATEGY-CRITICAL)
axiom lefschetz_lift_signed_cycle {p p'} (γ₊ γ₋ : SmoothForm n X (2*p)) (h_decomp : ...) :
    ∃ (γ'₊ γ'₋ : SmoothForm n X (2*p')), ...
```

### Hodge/Utils/BaranyGrinberg.lean (1 item)

```lean
-- Line 52: Bárány-Grinberg (⚠️ KEEP AS AXIOM - deep combinatorics, published 1981)
axiom barany_grinberg (v : ι → (Fin d → ℝ)) (hv : ∀ i j, |v i j| ≤ 1) (w : Fin d → ℝ) (hw : ‖w‖ ≤ 1/d) :
    ∃ (f : ι → ℤ), ...
```

## Deliverables

- [ ] Convert all 8 in `Microstructure.lean`
- [ ] Convert 2 in `SignedDecomp.lean`
- [ ] Convert 3 in `Main.lean`
- [ ] Keep `barany_grinberg` as axiom
- [ ] **Total: 14 items (13 to convert)**

## ⚠️ STRATEGY-CRITICAL ITEMS

These axioms encode the core mathematical substance:
1. **`signed_decomposition`** - Decomposing rational (p,p) forms into positive parts
2. **`harvey_lawson_fundamental_class`** - HL limit produces algebraic variety
3. **`lefschetz_lift_signed_cycle`** - Lefschetz lifting preserves decomposition

---

# 📊 Summary

| Agent | Files | Total Items | Must Convert | Can Keep |
|-------|-------|-------------|--------------|----------|
| **1** | Basic, Forms, Norms | 82 | 82 | 0 |
| **2** | Currents, FlatNorm, IntegralCurrents, Calibration | 44 | 44 | 0 |
| **3** | Grassmannian, Cone, TypeDecomp, Manifolds | 32 | 32 | 0 |
| **4** | GAGA, HarveyLawson, Bergman, SheafTheory, Lefschetz, FF, SV | 39 | 31 | 8 |
| **5** | Microstructure, SignedDecomp, Main, BaranyGrinberg | 14 | 13 | 1 |
| **TOTAL** | 22 files | **211** | **202** | **9** |

---

# 📋 Agent Prompts

## Agent 1 Prompt

```
You are Agent 1 working on the Hodge Conjecture Lean formalization.

## YOUR FILES
- Hodge/Basic.lean (28 axioms/opaques)
- Hodge/Analytic/Forms.lean (31 axioms/opaques)
- Hodge/Analytic/Norms.lean (23 axioms/opaques)

## YOUR TASK
Convert ALL 82 axioms and opaques to theorems and concrete definitions.

## KEY CONVERSIONS

### Hodge/Basic.lean (28 items)
- opaque SmoothForm → def using alternating maps on tangent bundle
- SmoothForm.instAddCommGroup/instModuleComplex/instModuleReal → instance proofs
- opaque smoothExtDeriv → def using Mathlib exterior derivative
- axioms smoothExtDeriv_add/smul → prove linearity from def
- axioms instAddCommGroupDeRhamCohomologyClass, instModuleDeRhamCohomologyClass → prove using Quotient API
- axiom instHMulDeRhamCohomologyClass → prove wedge product descends to quotient
- axioms ofForm_add/smul/neg/smul_real → prove using Quotient.liftOn
- opaque isRationalClass → def using actual rationality condition
- axioms isRationalClass_zero/add/smul_rat/mul → prove from def

### Hodge/Analytic/Forms.lean (31 items)
- opaque smoothWedge → def using exterior algebra wedge
- axioms smoothWedge_add_left/right/smul/assoc/comm → prove from def
- axiom smoothExtDeriv_wedge → prove Leibniz rule
- opaque unitForm → def as constant 1 form
- opaque hodgeStar → def using Hodge star operator
- axioms hodgeStar_add/smul/hodgeStar → prove from def
- opaque adjointDeriv → def as δ = ±*d*
- opaque laplacian → def as Δ = dδ + δd
- opaque lefschetzLambda → def using interior product with ω

### Hodge/Analytic/Norms.lean (23 items)
- opaque pointwiseComass → def using sSup { |ω(v)| : ‖v‖ ≤ 1 }
- axioms pointwiseComass_nonneg/zero/add_le/smul/continuous → prove from def
- axioms comass_add_le/smul/eq_zero_iff → prove from pointwiseComass
- opaque pointwiseInner → def using Hermitian inner product on forms
- opaque L2Inner → def as ∫ pointwiseInner dμ
- axioms L2Inner_add_left/smul_left/self_nonneg/comm/cauchy_schwarz → prove
- axiom energy_minimizer → prove or cite Hodge theory
- axiom trace_L2_control → prove Sobolev embedding

## RULES
- NO sorry, NO admit
- 🔴 **DO NOT RUN `lake build`** 🔴 — The coordinator runs builds, not you!
- Use Mathlib wherever possible
- Document non-obvious steps

## OUTPUT FORMAT
```lean
-- FILE: Hodge/Basic.lean
-- REPLACING: lines X-Y

<your code here>
```

Provide ALL 82 items.
```

## Agent 2 Prompt

```
You are Agent 2 working on the Hodge Conjecture Lean formalization.

## YOUR FILES
- Hodge/Analytic/Currents.lean (16 axioms/opaques)
- Hodge/Analytic/FlatNorm.lean (11 axioms/opaques)
- Hodge/Analytic/IntegralCurrents.lean (12 axioms/opaques)
- Hodge/Analytic/Calibration.lean (5 axioms/opaques)

## YOUR TASK
Convert ALL 44 axioms and opaques to theorems and concrete definitions.

## KEY CONVERSIONS

### Hodge/Analytic/Currents.lean (16 items)
- axiom map_add'/map_smul' → prove linearity of currents
- axiom zero → define zero current
- opaque add_curr/neg_curr/smul_curr → def as pointwise operations
- opaque mass → def as sSup { |T(ψ)| / comass(ψ) : comass(ψ) > 0 }
- axioms mass_nonneg/zero/neg/add_le/smul → prove from def
- axiom is_bounded → prove currents are bounded
- opaque boundary → def using Stokes
- axiom boundary_boundary → prove ∂∂ = 0

### Hodge/Analytic/FlatNorm.lean (11 items)
- opaque flatNorm → def as sInf { mass(S) + mass(R) : T = S + ∂R }
- axioms flatNorm_nonneg/zero/eq_zero_iff/neg/add_le/smul → prove from def
- axiom flatNorm_le_mass → prove by taking R = 0
- axiom eval_le_mass/eval_le_flatNorm → prove evaluation bounds
- axiom flatNorm_boundary_le → prove using ∂∂ = 0

### Hodge/Analytic/IntegralCurrents.lean (12 items)
- opaque isRectifiable → def using rectifiable sets from Mathlib
- axioms isRectifiable_empty/union → prove
- opaque IntegralPolyhedralChain → def as polyhedral chains with ℤ coefficients
- axioms polyhedral_add/zero/smul/boundary → prove closure properties
- axioms isIntegral_add/zero_current/smul/boundary → prove

### Hodge/Analytic/Calibration.lean (5 items)
- axiom wirtinger_comass_bound → prove ‖ω^p/p!‖ ≤ 1
- axiom calibration_inequality → prove T(ψ) ≤ mass(T)
- axiom spine_theorem → cite Harvey-Lawson
- axiom mass_lsc → prove lower semicontinuity
- axiom limit_is_calibrated → ⚠️ STRATEGY-CRITICAL

## RULES
- NO sorry, NO admit
- 🔴 **DO NOT RUN `lake build`** 🔴 — The coordinator runs builds, not you!
- Use Mathlib wherever possible

## OUTPUT FORMAT
```lean
-- FILE: Hodge/Analytic/Currents.lean
-- REPLACING: lines X-Y

<your code here>
```

Provide ALL 44 items.
```

## Agent 3 Prompt

```
You are Agent 3 working on the Hodge Conjecture Lean formalization.

## YOUR FILES
- Hodge/Analytic/Grassmannian.lean (11 axioms/opaques)
- Hodge/Kahler/Cone.lean (4 axioms/opaques)
- Hodge/Kahler/TypeDecomposition.lean (10 axioms/opaques)
- Hodge/Kahler/Manifolds.lean (7 axioms/opaques)

## YOUR TASK
Convert ALL 32 axioms and opaques to theorems and concrete definitions.

## KEY CONVERSIONS

### Hodge/Analytic/Grassmannian.lean (11 items)
- opaque IsVolumeFormOn → def as nonzero top form on subspace
- axiom IsVolumeFormOn_nonzero → prove from def
- axiom exists_volume_form_of_submodule_axiom → prove by constructing e₁∧...∧eₚ
- axiom simpleCalibratedForm → construct calibrated form
- axiom calibratedCone_hull_pointed → prove cone is pointed
- opaque distToCone → def as inf { ‖α - β‖ : β ∈ cone }
- opaque coneDefect → def as iSup of distToCone over x
- axiom distToCone_nonneg/coneDefect_nonneg → prove
- axiom radial_minimization/dist_cone_sq_formula → prove projection

### Hodge/Kahler/Cone.lean (4 items)
- axiom wirtinger_pairing → prove ⟨ω^p/p!, vol_V⟩ = 1
- axiom omegaPow_in_interior → prove using wirtinger_pairing
- axiom exists_uniform_interior_radius → prove using compactness
- axiom caratheodory_decomposition → prove using Carathéodory's theorem

### Hodge/Kahler/TypeDecomposition.lean (10 items)
- opaque isPQForm → def using Dolbeault type decomposition
- axiom zero_is_pq → prove 0 is (p,q) for all p,q
- axiom isPQForm_wedge → prove wedge preserves type
- axiom omega_is_1_1_axiom → prove ω is (1,1)
- opaque kahlerPow → def as ω^p / p!
- axiom unitForm_is_0_0/omega_pow_is_p_p_axiom → prove type
- axiom omega_pow_IsFormClosed/is_rational → prove from Kähler
- axiom IsFormClosed_omegaPow_scaled → prove scaling preserves

### Hodge/Kahler/Manifolds.lean (7 items)
- axiom kahlerMetric_symm → prove Hermitian symmetry
- axiom isRationalClass_wedge → prove product of rational is rational
- axiom omega_isClosed/is_rational → prove from Kähler condition
- axiom zero_is_rational → prove 0 is rational
- axiom unitForm_isClosed/is_rational → prove d(1) = 0

## RULES
- NO sorry, NO admit
- 🔴 **DO NOT RUN `lake build`** 🔴 — The coordinator runs builds, not you!

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
- Hodge/Classical/GAGA.lean (10 axioms/opaques)
- Hodge/Classical/HarveyLawson.lean (10 axioms/opaques)
- Hodge/Classical/Lefschetz.lean (7 axioms/opaques)
- Hodge/Analytic/SheafTheory.lean (5 axioms/opaques)
- Hodge/Classical/Bergman.lean (4 axioms/opaques)
- Hodge/Classical/FedererFleming.lean (2 axioms/opaques)
- Hodge/Classical/SerreVanishing.lean (1 axiom)

## YOUR TASK
Convert 31 of 39 items. Keep these 8 as axioms (classical pillars):
- serre_gaga, harvey_lawson_theorem, harvey_lawson_represents
- hard_lefschetz_isomorphism, hard_lefschetz_inverse_form
- tian_convergence, federer_fleming_compactness, serre_vanishing

## KEY CONVERSIONS

### Hodge/Classical/GAGA.lean (10 items, keep serre_gaga)
- opaque IsZariskiClosed → def using polynomial vanishing
- axioms IsAlgebraicSet_empty/univ/union/intersection/isClosed → prove
- axiom IsAlgebraicSet_isAnalyticSet → prove algebraic ⊂ analytic
- axiom FundamentalClassSet_additive/rational → prove

### Hodge/Classical/HarveyLawson.lean (10 items, keep hl_theorem/represents)
- opaque IsAnalyticSet → def using local analytic equations
- axioms IsAnalyticSet_empty/univ/union/inter/isClosed/nontrivial → prove
- axiom flat_limit_of_cycles_is_cycle → ⚠️ STRATEGY-CRITICAL

### Hodge/Classical/Lefschetz.lean (7 items, keep hard_lefschetz_*)
- axiom ofForm_wedge_add → prove wedge on cohomology
- opaque lefschetz_operator → def as multiplication by [ω]
- axiom lefschetz_operator_eval → prove evaluation
- axiom hard_lefschetz_bijective → prove bijectivity
- opaque lefschetz_inverse_cohomology → def as inverse

### Hodge/Analytic/SheafTheory.lean (5 items)
- axiom SheafCohomology.finiteDimensional' → prove
- axiom structureSheafAsCoherent/h0_structure_sheaf_nonvanishing → prove
- axiom structureSheaf_exists/idealSheaf_exists → prove

### Hodge/Classical/Bergman.lean (4 items, keep tian_convergence)
- axiom IsHolomorphic_add/smul → prove linearity
- axiom jet_surjectivity → prove

### Hodge/Classical/FedererFleming.lean (2 items, keep compactness)
- axiom deformation_theorem → prove or cite

## RULES
- NO sorry, NO admit
- 🔴 **DO NOT RUN `lake build`** 🔴 — The coordinator runs builds, not you!

## OUTPUT FORMAT
```lean
-- FILE: Hodge/Classical/GAGA.lean
-- REPLACING: lines X-Y

<your code here>
```

Provide ALL 31 items to convert.
```

## Agent 5 Prompt

```
You are Agent 5 working on the Hodge Conjecture Lean formalization.

## YOUR FILES
- Hodge/Kahler/Microstructure.lean (8 axioms/opaques)
- Hodge/Kahler/SignedDecomp.lean (2 axioms/opaques)
- Hodge/Kahler/Main.lean (3 axioms/opaques)
- Hodge/Utils/BaranyGrinberg.lean (1 axiom - keep as is)

## YOUR TASK
Convert 13 of 14 items. Keep `barany_grinberg` as axiom.

## KEY CONVERSIONS

### Hodge/Kahler/SignedDecomp.lean (2 items)
- axiom form_is_bounded → prove using compactness of X
- axiom signed_decomposition → ⚠️ STRATEGY-CRITICAL: decompose rational (p,p) forms

### Hodge/Kahler/Microstructure.lean (8 items)
- axiom local_sheet_realization → prove local complex submanifold exists
- axiom integer_transport → prove using Barany-Grinberg
- opaque SmoothForm.pairing → def as integration pairing
- opaque RawSheetSum.toIntegralCurrent → def conversion to current
- axiom gluing_estimate/gluing_flat_norm_bound/calibration_defect_from_gluing → prove bounds
- axiom cubulation_exists → prove mesh construction

### Hodge/Kahler/Main.lean (3 items)
- axiom harvey_lawson_fundamental_class → ⚠️ STRATEGY-CRITICAL: HL limit is algebraic
- axiom omega_pow_represents_multiple → prove ωᵖ represents scalar class
- axiom lefschetz_lift_signed_cycle → ⚠️ STRATEGY-CRITICAL: Lefschetz lift

## ⚠️ STRATEGY-CRITICAL ITEMS (highest priority!)

These encode the core mathematical substance of the proof:
1. `signed_decomposition` - decomposing rational (p,p) forms into positive parts
2. `harvey_lawson_fundamental_class` - HL limit produces algebraic variety
3. `lefschetz_lift_signed_cycle` - Lefschetz lifting preserves decomposition

## RULES
- NO sorry, NO admit
- 🔴 **DO NOT RUN `lake build`** 🔴 — The coordinator runs builds, not you!

## OUTPUT FORMAT
```lean
-- FILE: Hodge/Kahler/SignedDecomp.lean
-- REPLACING: lines X-Y

<your code here>
```

Provide ALL 13 items to convert.
```

---

# 📈 Progress Tracker

**Last Updated:** 2024-12-31
**Build Status:** ✅ PASSES

| Agent | Files | Items | To Convert | Status |
|-------|-------|-------|------------|--------|
| 1 | Basic, Forms, Norms | 82 | 82 | 🔴 Not started |
| 2 | Currents, FlatNorm, IntegralCurrents, Calibration | 44 | 44 | 🔴 Not started |
| 3 | Grassmannian, Cone, TypeDecomp, Manifolds | 32 | 32 | 🔴 Not started |
| 4 | GAGA, HarveyLawson, Bergman, SheafTheory, Lefschetz, FF, SV | 39 | 31 | 🔴 Not started |
| 5 | Microstructure, SignedDecomp, Main, BaranyGrinberg | 14 | 13 | 🔴 Not started |
| **TOTAL** | 22 files | **211** | **202** | — |

## Classical Pillars (keep as axioms)

These 9 axioms represent deep published theorems that can remain as axioms:
1. `serre_gaga` - Serre 1956
2. `harvey_lawson_theorem` - Harvey-Lawson 1982
3. `harvey_lawson_represents` - Harvey-Lawson 1982
4. `hard_lefschetz_isomorphism` - Lefschetz 1924, Hodge 1941
5. `hard_lefschetz_inverse_form` - Lefschetz 1924, Hodge 1941
6. `tian_convergence` - Tian 1990
7. `federer_fleming_compactness` - Federer-Fleming 1960
8. `serre_vanishing` - Serre 1955
9. `barany_grinberg` - Bárány-Grinberg 1981

## Strategy-Critical Axioms (must convert!)

These 6 axioms encode the core mathematical substance and MUST be proven:
1. `signed_decomposition` - Agent 5
2. `harvey_lawson_fundamental_class` - Agent 5
3. `lefschetz_lift_signed_cycle` - Agent 5
4. `flat_limit_of_cycles_is_cycle` - Agent 4
5. `limit_is_calibrated` - Agent 2
