# Infrastructure Axioms: 5-Track Proof Guide

## Overview

This document provides prompts for proving ~45 infrastructure axioms across 5 tracks.
These are **definitional truths** or **basic mathematical facts** that Mathlib doesn't yet support.
They are NOT deep theorems — they are plumbing.

**Usage:** Tell an agent: "Work on Track X from `INFRASTRUCTURE_AXIOMS_PROMPT.md`"

---

## Global Rules (Apply to ALL Tracks)

### 1. NO SHORTCUTS
- **NEVER use `sorry`** — the goal is to eliminate axioms
- **NEVER use `trivial`** unless it genuinely closes a goal
- **NEVER axiomatize** — convert axioms to theorems/definitions

### 2. BUILD STRATEGY
- **Prefer file builds**: `lake build Hodge.{ModuleName}`
- Run full build only when adding imports or changing signatures
- Always check build output; fix errors before proceeding

### 3. MATHLIB FIRST
Before writing any proof:
```bash
grep -r "KEYWORD" .lake/packages/mathlib/Mathlib/ | head -30
```
Search paths:
- `Mathlib.Analysis.Normed.*` — norm properties
- `Mathlib.Analysis.InnerProductSpace.*` — inner products
- `Mathlib.Geometry.Manifold.*` — manifold definitions
- `Mathlib.Topology.*` — compactness, continuity
- `Mathlib.LinearAlgebra.*` — vector space operations

### 4. PROOF APPROACH
1. Read the axiom and understand its mathematical content
2. Check if Mathlib has the result (or a variant)
3. If purely definitional, provide the definition directly
4. If a basic property, prove from existing lemmas
5. Build incrementally — test each lemma compiles

### 5. SUCCESS CRITERIA
- `axiom X` → `theorem X` or `def X`
- No `sorry` in the proof
- `lake build Hodge.{ModuleName}` succeeds

---

# Track 1: Smooth Forms and Norms

**File:** `Hodge/Analytic/Norms.lean`
**Axioms:** 17
**Difficulty:** Medium — requires understanding of normed spaces

## Axioms to Prove

### 1.1 Comass Properties (5 axioms)

```lean
-- Line 73: Continuity of pointwise comass
axiom pointwiseComass_continuous {k : ℕ} (α : SmoothForm n X k) :
    Continuous (pointwiseComass α)
```
**Strategy:** Use Berge's Maximum Theorem. The supremum of continuous functions over a compact parameterized set varies continuously. Reference: Berge (1963).

```lean
-- Line 91: Pointwise comass of zero
axiom pointwiseComass_zero {k : ℕ} (x : X) :
    pointwiseComass (0 : SmoothForm n X k) x = 0
```
**Strategy:** The zero form evaluates to 0 everywhere. Show the set `{r | ...}` is `{0}` and `sSup {0} = 0`.

```lean
-- Line 96: Global comass of zero
axiom comass_zero {k : ℕ} : comass (0 : SmoothForm n X k) = 0
```
**Strategy:** Follows from `pointwiseComass_zero` and `iSup` of constant zero.

```lean
-- Line 121: Triangle inequality
axiom comass_add_le {k : ℕ} (α β : SmoothForm n X k) :
    comass (α + β) ≤ comass α + comass β
```
**Strategy:** Use `norm_add_le` at each point, then propagate through `sSup` and `iSup`.

```lean
-- Line 126: Homogeneity
axiom comass_smul {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    comass (r • α) = |r| * comass α
```
**Strategy:** Use `norm_smul` and homogeneity of supremum.

### 1.2 Comass Boundedness (1 axiom)

```lean
-- Line 131
axiom comass_bddAbove {k : ℕ} (α : SmoothForm n X k) :
    BddAbove (Set.range (pointwiseComass α))
```
**Strategy:** On compact manifolds, continuous functions are bounded. Use `pointwiseComass_continuous` (once proven) and `IsCompact.bddAbove_range`.

### 1.3 Normed Space Instances (4 axioms)

```lean
-- Lines 141-166
axiom smoothFormTopologicalSpace_exists (k : ℕ) : Nonempty (TopologicalSpace (SmoothForm n X k))
axiom smoothFormMetricSpace_exists (k : ℕ) : Nonempty (MetricSpace (SmoothForm n X k))
axiom smoothFormNormedAddCommGroup_exists (k : ℕ) : Nonempty (NormedAddCommGroup (SmoothForm n X k))
axiom smoothFormNormedSpace_exists (k : ℕ) : Nonempty (NormedSpace ℝ (SmoothForm n X k))
```
**Strategy:** Construct these instances directly using `comass` as the norm. You need:
- Triangle inequality (`comass_add_le`)
- Homogeneity (`comass_smul`)
- Positive definiteness (need `comass α = 0 ↔ α = 0`)

Use Mathlib's `NormedAddCommGroup.ofCore` or similar constructors.

### 1.4 Inner Product and L2 (7 axioms)

```lean
-- Line 172
axiom kahlerMetricDual (x : X) (α β : TangentSpace (𝓒_complex n) x →ₗ[ℂ] ℂ) : ℂ
```
**Strategy:** This should be a **definition**, not an axiom. Define it using the musical isomorphism from Kähler geometry.

```lean
-- Line 176
axiom pointwiseInner {k : ℕ} (α β : SmoothForm n X k) (x : X) : ℝ
```
**Strategy:** This should be a **definition**. Use the induced inner product on exterior powers.

```lean
-- Line 184
axiom innerL2 {k : ℕ} (α β : SmoothForm n X k) : ℝ
```
**Strategy:** Define as `∫ x, pointwiseInner α β x * volume_form x`. Need measure theory.

```lean
-- Line 200
axiom energy_minimizer {k : ℕ} (α γ_harm : SmoothForm n X k) :
    isClosed α → isHarmonic γ_harm → energy α = energy γ_harm + energy (α - γ_harm)
```
**Strategy:** This is the Pythagorean theorem for Hodge decomposition. Requires orthogonality of harmonic and exact forms.

```lean
-- Line 206
axiom pointwiseInner_nonneg {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseInner α α x ≥ 0
```
**Strategy:** Follows from positive-definiteness of the Kähler metric.

```lean
-- Line 211
axiom energy_nonneg {k : ℕ} (α : SmoothForm n X k) : energy α ≥ 0
```
**Strategy:** Integral of non-negative function is non-negative.

```lean
-- Line 222
axiom trace_L2_control {k : ℕ} (α : SmoothForm n X k) :
    ∃ C : ℝ, C > 0 ∧ comass α ≤ C * normL2 α
```
**Strategy:** Sobolev embedding on compact manifolds. Deep result but standard.

---

# Track 2: Grassmannian and Cone Geometry

**Files:** `Hodge/Analytic/Grassmannian.lean`, `Hodge/Kahler/Cone.lean`
**Axioms:** 6
**Difficulty:** Medium — convex geometry and projection theory

## Axioms to Prove

### 2.1 Simple Calibrated Forms (1 axiom)

```lean
-- Grassmannian.lean:64
axiom simpleCalibratedForm_raw (p : ℕ) (x : X) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x)) :
    (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℂ] ℂ
```
**Strategy:** This should be a **definition**. Construct the volume form of V:
1. Choose an orthonormal basis {e₁, ..., e_p} of V
2. Return the exterior product e₁* ∧ Je₁* ∧ ... ∧ e_p* ∧ Je_p*

### 2.2 Cone Defect (1 axiom)

```lean
-- Grassmannian.lean:106
axiom coneDefect (p : ℕ) (α : SmoothForm n X (2 * p)) : ℝ
```
**Strategy:** This should be a **definition**:
```lean
def coneDefect (p : ℕ) (α : SmoothForm n X (2 * p)) : ℝ :=
  Real.sqrt (∫ x, (distToCone p α x)^2)
```

### 2.3 Distance Formula (1 axiom)

```lean
-- Grassmannian.lean:153
axiom dist_cone_sq_formula (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) :
    (distToCone p α x)^2 = (pointwiseNorm α x)^2 -
      (sSup { r | ∃ ξ ∈ simpleCalibratedForms p x, r = max 0 (pointwiseInner α ξ x) })^2
```
**Strategy:** This is projection onto a closed convex cone. Use:
- `Metric.infDist` properties from Mathlib
- The formula for projection onto a cone: `proj_C(x) = argmin_{y∈C} ‖x-y‖`
- For cones generated by unit vectors: `dist(x,C)² = ‖x‖² - max(0, max_ξ⟨x,ξ⟩)²`

### 2.4 Wirtinger Inequality (1 axiom)

```lean
-- Cone.lean:78
axiom wirtinger_pairing_axiom (p : ℕ) (x : X) (ξ : SmoothForm n X (2 * p))
    (hξ : ξ ∈ simpleCalibratedForms p x) :
    pointwiseInner (omegaPow_point p x) ξ x = 1
```
**Strategy:** The Wirtinger inequality: `ω^p` restricted to any complex p-plane has volume exactly 1. This requires:
1. Knowing `omegaPow_point` is `ω^p/p!`
2. The normalization of simple calibrated forms
3. Integration over the plane gives 1

### 2.5 Interior of Cone (1 axiom)

```lean
-- Cone.lean:105
axiom omegaPow_in_interior (p : ℕ) (x : X) :
    (omegaPow_point p x) ∈ interior (stronglyPositiveCone p x)
```
**Strategy:** From `wirtinger_pairing_axiom`, ω^p pairs with value 1 > 0 with all generators. In finite dimensions, this implies membership in the interior. Use Mathlib's `interior_mem_nhds` and convex cone theory.

### 2.6 Uniform Radius (1 axiom)

```lean
-- Cone.lean:121
axiom exists_uniform_interior_radius [CompactSpace X] (p : ℕ) :
    ∃ r : ℝ, r > 0 ∧ ∀ x : X, ball (omegaPow_point p x) r ⊆ stronglyPositiveCone p x
```
**Strategy:** 
1. For each x, `omegaPow_in_interior` gives an open ball around ω^p(x) in the cone
2. The radius function x ↦ sup{r | ball ⊆ cone} is continuous
3. Use `compact_pos_has_pos_inf` (already proven in the file!) to get uniform minimum

---

# Track 3: Holomorphic Line Bundles

**File:** `Hodge/Classical/Bergman.lean`
**Axioms:** 14
**Difficulty:** High — holomorphic geometry infrastructure

## Axioms to Prove

### 3.1 Bundle Operations (2 axioms)

```lean
-- Line 50
axiom HolomorphicLineBundle.tensor_has_local_trivializations {L₁ L₂ : HolomorphicLineBundle n X} (x : X) :
  ∃ (U : Opens X) (hx : x ∈ U), Nonempty (∀ y ∈ U, (L₁.Fiber y ⊗[ℂ] L₂.Fiber y) ≃ₗ[ℂ] ℂ)
```
**Strategy:** Tensor product of local trivializations. If L₁ ≃ U × ℂ and L₂ ≃ U × ℂ locally, then L₁ ⊗ L₂ ≃ U × (ℂ ⊗ ℂ) ≃ U × ℂ.

```lean
-- Line 67
axiom trivial_bundle_has_local_trivializations (x : X) :
  ∃ (U : Opens X) (hx : x ∈ U), Nonempty (∀ y ∈ U, ℂ ≃ₗ[ℂ] ℂ)
```
**Strategy:** Trivial! Just use the identity map on any open neighborhood.

### 3.2 Holomorphic Section Operations (4 axioms)

```lean
-- Line 104
axiom IsHolomorphic_add (s₁ s₂ : Section L) :
  IsHolomorphic s₁ → IsHolomorphic s₂ → IsHolomorphic (s₁ + s₂)
```
**Strategy:** Sum of holomorphic functions is holomorphic. Use `MDifferentiable.add`.

```lean
-- Line 108
axiom IsHolomorphic_zero : IsHolomorphic (0 : Section L)
```
**Strategy:** Zero function is holomorphic. Use `mdifferentiable_const`.

```lean
-- Line 112
axiom IsHolomorphic_smul (c : ℂ) (s : Section L) :
  IsHolomorphic s → IsHolomorphic (c • s)
```
**Strategy:** Scalar multiple of holomorphic is holomorphic. Use `MDifferentiable.const_smul`.

```lean
-- Line 214
axiom IsHolomorphic_tensor {s₁ : Section L₁} {s₂ : Section L₂} :
  IsHolomorphic s₁ → IsHolomorphic s₂ → IsHolomorphic (fun x => s₁ x ⊗ₜ[ℂ] s₂ x)
```
**Strategy:** Product of holomorphic functions is holomorphic. The tensor product is bilinear, so this reduces to the product rule.

### 3.3 Differential Operators (3 axioms)

```lean
-- Line 123
axiom partial_deriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1)
```
**Strategy:** This should be a **definition**. The ∂ operator on complex manifolds. Define using:
- Local coordinates: ∂ω = Σᵢ (∂ω/∂zᵢ) dzᵢ
- Or use the exterior derivative and type decomposition

```lean
-- Line 126
axiom partial_bar_deriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1)
```
**Strategy:** The ∂̄ operator. Define as `partial_bar_deriv ω = Σᵢ (∂ω/∂z̄ᵢ) dz̄ᵢ`.

```lean
-- Line 129
axiom log_h {L : HolomorphicLineBundle n X} (h : HermitianMetric L) : SmoothForm n X 0
```
**Strategy:** This should be a **definition**. In local frames, log h is the log of the metric component: if h(e,e) = |e|²_h in a local frame e, then log_h = log(h(e,e)).

### 3.4 Bergman Kernel (2 axioms)

```lean
-- Line 160
axiom log_KM (L : HolomorphicLineBundle n X) [IsAmple L] (M : ℕ) (h : HermitianMetric (L.power M)) :
    SmoothForm n X 0
```
**Strategy:** The Bergman kernel K_M(x) = Σᵢ |sᵢ(x)|²_h where {sᵢ} is an orthonormal basis of H⁰(X, L^M). Define log_KM as log(K_M).

```lean
-- Line 176
axiom tian_convergence (L : HolomorphicLineBundle n X) [IsAmple L]
    (h : ∀ M, HermitianMetric (L.power M)) :
    ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, dist_form ((1/M : ℝ) • BergmanMetric L M (h M)) K.omega_form ≤ ε
```
**Strategy:** This is **Tian's Theorem** (1990) — a deep result. Keep as axiom or cite.

### 3.5 Jet Spaces (2 axioms)

```lean
-- Line 186
axiom SectionsVanishingToOrder (L : HolomorphicLineBundle n X) (x : X) (k : ℕ) :
    Submodule ℂ ↥(HolomorphicSection L)
```
**Strategy:** This should be a **definition**:
```lean
def SectionsVanishingToOrder L x k : Submodule ℂ (HolomorphicSection L) :=
  { carrier := { s | ∀ |α| ≤ k, (∂^α s)(x) = 0 }
    ... }
```

```lean
-- Line 207
axiom jet_surjectivity (L : HolomorphicLineBundle n X) [IsAmple L] (x : X) (k : ℕ) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, Function.Surjective (jet_eval (L := L.power M) x k)
```
**Strategy:** This follows from Serre vanishing. Actually, there's already a theorem `jet_surjectivity_from_serre` that proves this from `serre_vanishing`! Just need to connect them.

### 3.6 L2 Inner Product (1 axiom)

```lean
-- Line 141
axiom L2InnerProduct (L : HolomorphicLineBundle n X) (h : HermitianMetric L)
    (s t : Section L) : ℂ
```
**Strategy:** This should be a **definition**:
```lean
def L2InnerProduct L h s t : ℂ :=
  ∫ x, h.inner x (s x) (t x) * volume_form x
```

---

# Track 4: Sheaf Cohomology

**File:** `Hodge/Classical/SerreVanishing.lean`
**Axioms:** 8
**Difficulty:** Very High — major Mathlib gap

## Important Note

Sheaf cohomology is a **major gap in Mathlib**. These axioms represent infrastructure that would take months to formalize properly. Consider keeping most of these as axioms.

## Axioms to Prove (or Keep)

### 4.1 Core Sheaf Theory (4 axioms)

```lean
-- Line 16
axiom CoherentSheaf (n : ℕ) (X : Type u) [...] : Type u
```
**Status:** KEEP AS AXIOM. Coherent sheaves require:
- Sheaf theory on complex manifolds
- Coherence condition (locally finitely generated)
- No Mathlib support

```lean
-- Line 22
axiom SheafCohomology (F : CoherentSheaf n X) (q : ℕ) : Type u
```
**Status:** KEEP AS AXIOM. Čech or derived functor cohomology. Major project.

```lean
-- Lines 28-40: instAddCommGroup, instModule
```
**Status:** KEEP AS AXIOMS. Standard algebraic structure on cohomology.

### 4.2 Sheaf Operations (2 axioms)

```lean
-- Line 56
axiom tensorWithSheaf (L : HolomorphicLineBundle n X) (F : CoherentSheaf n X) : CoherentSheaf n X
```
**Status:** KEEP AS AXIOM. Tensor product of sheaves.

```lean
-- Line 60
axiom idealSheaf (x : X) (k : ℕ) : CoherentSheaf n X
```
**Status:** KEEP AS AXIOM. The sheaf of functions vanishing to order k at x.

### 4.3 Main Theorems (2 axioms)

```lean
-- Line 67
axiom serre_vanishing (L : HolomorphicLineBundle n X) [IsAmple L]
    (F : CoherentSheaf n X) (q : ℕ) (hq : q > 0) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, vanishes (tensorWithSheaf (L.power M) F) q
```
**Status:** KEEP AS AXIOM. This is **Serre's Vanishing Theorem** — a major result in algebraic geometry.

```lean
-- Line 75
axiom jet_surjectivity_criterion {L : HolomorphicLineBundle n X} {x : X} {k : ℕ} :
    vanishes (tensorWithSheaf L (idealSheaf x k)) 1 →
    Function.Surjective (jet_eval (L := L) x k)
```
**Status:** KEEP AS AXIOM. Long exact sequence in cohomology.

---

# Track 5: Type Decomposition and Calibration

**Files:** `Hodge/Kahler/TypeDecomposition.lean`, `Hodge/Analytic/Calibration.lean`
**Axioms:** 6
**Difficulty:** Medium

## Axioms to Prove

### 5.1 Type Decomposition (1 axiom + 2 sorries)

```lean
-- TypeDecomposition.lean:15
axiom isPQForm (n : ℕ) (X : Type*) [...] (p q : ℕ) {k : ℕ} (h : p + q = k) (ω : SmoothForm n X k) : Prop
```
**Strategy:** This should be a **definition**. A form ω is (p,q) if in local holomorphic coordinates:
```
ω = Σ_{|I|=p, |J|=q} ω_{IJ} dz^I ∧ dz̄^J
```
Define using the type decomposition of the exterior algebra.

```lean
-- TypeDecomposition.lean:34
theorem omega_is_1_1 : isPPForm' n X 1 (K.omega_form) := sorry
```
**Strategy:** The Kähler form is by definition a (1,1)-form. This should follow from the definition of `KahlerManifold`.

```lean
-- TypeDecomposition.lean:43
def omegaPow (n : ℕ) (X : Type*) [...] (p : ℕ) : SmoothForm n X (2 * p) := sorry
```
**Strategy:** Define as the p-fold wedge product of the Kähler form:
```lean
def omegaPow n X p : SmoothForm n X (2 * p) :=
  match p with
  | 0 => 1  -- unit form
  | p + 1 => K.omega_form ∧ omegaPow n X p
```

### 5.2 Calibrating Forms (1 axiom)

```lean
-- Calibration.lean:62
axiom KählerCalibration_exists (p : ℕ) :
    ∃ (ψ : CalibratingForm n X (2 * p)), comass ψ.form = 1
```
**Strategy:** The form ω^p/p! is calibrating. Need to show:
1. It's closed (d(ω^p) = 0 since dω = 0)
2. Comass = 1 (Wirtinger inequality: achieves equality on complex p-planes)

### 5.3 Calibration Theorems (4 axioms)

```lean
-- Calibration.lean:90
axiom calibration_inequality (T : Current n X k) (ψ : CalibratingForm n X k) :
    T ψ.form ≤ T.mass
```
**Strategy:** This is the **fundamental inequality** of calibration theory:
|T(ψ)| ≤ mass(T) · comass(ψ) ≤ mass(T) · 1 = mass(T)

```lean
-- Calibration.lean:116
axiom spine_theorem (T S G : Current n X k) (ψ : CalibratingForm n X k)
    (h_decomp : T = S - G) (h_calib : isCalibrated S ψ) :
    calibrationDefect T ψ ≤ 2 * G.mass
```
**Strategy:** If T = S - G with S calibrated:
- defect(T) = mass(T) - T(ψ) = mass(S-G) - (S-G)(ψ)
- ≤ mass(S) + mass(G) - S(ψ) + G(ψ)
- = 0 + mass(G) + G(ψ) ≤ 2·mass(G)

```lean
-- Calibration.lean:123
axiom mass_lsc (T : ℕ → Current n X k) (T_limit : Current n X k) :
    Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0) →
    T_limit.mass ≤ liminf (fun i => (T i).mass) atTop
```
**Strategy:** Lower semicontinuity of mass under flat convergence. This is **Federer-Fleming**. Keep as axiom or cite.

```lean
-- Calibration.lean:130
axiom limit_is_calibrated (T : ℕ → Current n X k) (T_limit : Current n X k) (ψ : CalibratingForm n X k)
    (h_defect_vanish : Tendsto (fun i => calibrationDefect (T i) ψ) atTop (nhds 0))
    (h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    isCalibrated T_limit ψ
```
**Strategy:** Combine:
1. `mass_lsc`: mass(T_limit) ≤ liminf mass(T_i)
2. Continuity: T_limit(ψ) = lim T_i(ψ) (linear functional is continuous)
3. Defect → 0: mass(T_i) - T_i(ψ) → 0, so mass(T_i) → T_i(ψ)
4. Therefore: mass(T_limit) ≤ liminf T_i(ψ) = T_limit(ψ)
5. Combined with `calibration_inequality`: equality holds

---

# Summary Table

| Track | File(s) | Axioms | Difficulty | Key Dependencies |
|-------|---------|--------|------------|------------------|
| 1 | Norms.lean | 17 | Medium | Normed space theory |
| 2 | Grassmannian.lean, Cone.lean | 6 | Medium | Convex geometry |
| 3 | Bergman.lean | 14 | High | Complex geometry |
| 4 | SerreVanishing.lean | 8 | Very High | Major Mathlib gap |
| 5 | TypeDecomposition.lean, Calibration.lean | 6 | Medium | Form theory |

## Recommended Order

1. **Track 5** (Type Decomposition) — foundational definitions needed elsewhere
2. **Track 1** (Norms) — enables metric space structure
3. **Track 2** (Grassmannian/Cone) — depends on Track 1
4. **Track 3** (Line Bundles) — mostly independent
5. **Track 4** (Sheaf Cohomology) — keep as axioms, major Mathlib gap

## Quick Reference: Which to Keep as Axioms

**Definitely keep as axioms (deep theorems):**
- `serre_vanishing` — Serre's theorem
- `tian_convergence` — Tian's theorem
- `mass_lsc` — Federer-Fleming
- All of Track 4 (sheaf cohomology infrastructure)

**Convert to definitions:**
- `pointwiseInner`, `innerL2`, `kahlerMetricDual`
- `coneDefect`
- `simpleCalibratedForm_raw`
- `isPQForm`, `omegaPow`
- `partial_deriv`, `partial_bar_deriv`, `log_h`
- `SectionsVanishingToOrder`, `L2InnerProduct`

**Prove from Mathlib:**
- `comass_zero`, `pointwiseComass_zero`
- `comass_add_le`, `comass_smul`
- Normed space instances
- `IsHolomorphic_add`, `IsHolomorphic_zero`, `IsHolomorphic_smul`
- `calibration_inequality`, `spine_theorem`

