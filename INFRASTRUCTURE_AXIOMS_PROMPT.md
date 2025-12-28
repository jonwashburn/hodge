# Infrastructure Axioms: 5-Track Proof Guide

## Overview

This document provides prompts for proving ~45 infrastructure axioms across 5 tracks.
These are **definitional truths** or **basic mathematical facts** that Mathlib doesn't yet support.
They are NOT deep theorems — they are plumbing.

**Usage:** Tell an agent: "Work on Track X from `INFRASTRUCTURE_AXIOMS_PROMPT.md`"

Safeguards against sub-par work. The goal is to formalize reality as rigorously as possilbe. No shortcuts. No axioms, sorries, admits or trivial proofs. We are going to finish this fully, so no declaring success early. We are not stopping unti the job is done - as many sessions as it takes. 

@Hodge-v6-w-Jon-Update-MERGED.tex  this is the written proof to base on

---

## 📊 PROGRESS TRACKER (Updated: Dec 27, 2024)

| Track | Description | Converted | Remaining | Progress |
|-------|-------------|-----------|-----------|----------|
| 1 | Norms.lean | 12 | 5 | 🟡 70% |
| 2 | Grassmannian + Cone | 0 | 6 | 🔴 0% |
| 3 | Bergman.lean | 10 | 4 | 🟢 71% |
| 4A | Sheaf Types | 2 | 0 | 🟢 100% |
| 4B | Sheaf Algebra | 2 | 0 | 🟢 100% |
| 4C | Sheaf Operations | 2 | 0 | 🟢 100% |
| 4D | Sheaf Theorems | 2 | 0 | 🟢 100% |
| 5 | Calibration | 7 | 3 | 🟢 70% |
| **TOTAL** | | **37** | **18** | **67%** |

### Priority Order
1. **Track 2** — 0% done, blocks cone geometry
2. **Track 4A** — Start sheaf infrastructure
3. **Track 1 remaining** — Finish normed space instances
4. **Track 4B + 4C** — Can parallelize after 4A
5. **Track 4D** — Serre vanishing (hardest)

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

# Track 2: Grassmannian and Cone Geometry (PRIORITY: HIGH)

**Files:** `Hodge/Analytic/Grassmannian.lean`, `Hodge/Kahler/Cone.lean`
**Axioms:** 6
**Difficulty:** Medium — convex geometry and projection theory
**Status:** 🔴 0% complete — needs immediate attention

## Dependencies
- Requires Track 1 definitions (`pointwiseInner`, `pointwiseNorm`)
- Required by: cone-positive class detection, signed decomposition

---

## Axioms to Prove

### 2.1 Simple Calibrated Forms (1 axiom)

```lean
-- Grassmannian.lean:68
axiom simpleCalibratedForm_raw (p : ℕ) (x : X) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x)) :
    (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℂ] ℂ
```

**Strategy:** Convert to a **definition**. This is the volume form of a complex p-plane V.

```lean
/-- The simple calibrated form for a complex p-plane V.
    This is the volume form: e₁* ∧ Je₁* ∧ ... ∧ e_p* ∧ Je_p*
    where {e₁, ..., e_p} is an orthonormal basis of V. -/
def simpleCalibratedForm_raw (p : ℕ) (x : X)
    (V : Submodule ℂ (TangentSpace (𝓒_complex n) x)) :
    (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℂ] ℂ := by
  -- Step 1: Get an orthonormal basis of V
  haveI : FiniteDimensional ℂ V := sorry  -- V has dimension p
  let basis := OrthonormalBasis.mk sorry sorry  -- orthonormal basis of V
  -- Step 2: Build dual covectors e_i* and (Je_i)*
  -- Step 3: Take exterior product
  sorry
```

**Mathlib references:**
- `Mathlib.Analysis.InnerProductSpace.GramSchmidt` — orthonormal bases
- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic` — exterior algebra
- `Mathlib.LinearAlgebra.Dual` — dual vectors

**Build:** `lake build Hodge.Analytic.Grassmannian`

### 2.2 Cone Defect (1 axiom)

```lean
-- Grassmannian.lean:126
axiom coneDefect (p : ℕ) (α : SmoothForm n X (2 * p)) : ℝ
```

**Strategy:** Convert to a **definition**:

```lean
/-- The global cone defect: L2 norm of pointwise distance to calibrated cone. -/
def coneDefect (p : ℕ) (α : SmoothForm n X (2 * p)) : ℝ :=
  Real.sqrt (∫ x, (distToCone p α x)^2 ∂μ)  -- need volume measure μ
```

**Note:** The integration requires a measure on X. Use the Kähler volume form:
```lean
-- In terms of existing infrastructure:
def coneDefect (p : ℕ) (α : SmoothForm n X (2 * p)) : ℝ :=
  Real.sqrt (innerL2 (fun x => distToCone p α x) (fun x => distToCone p α x))
```

**Build:** `lake build Hodge.Analytic.Grassmannian`

### 2.3 Distance Formula (1 axiom)

```lean
-- Grassmannian.lean:173
axiom dist_cone_sq_formula (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) :
    (distToCone p α x)^2 = (pointwiseNorm α x)^2 -
      (sSup { r | ∃ ξ ∈ simpleCalibratedForms p x, r = max 0 (pointwiseInner α ξ x) })^2
```

**Strategy:** This is the projection formula for a closed convex cone.

**Proof outline:**
```lean
theorem dist_cone_sq_formula (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) :
    (distToCone p α x)^2 = (pointwiseNorm α x)^2 -
      (sSup { r | ∃ ξ ∈ simpleCalibratedForms p x, r = max 0 (pointwiseInner α ξ x) })^2 := by
  -- The calibrated cone C is generated by unit simple forms ξ
  -- For any closed convex cone C with unit generators:
  --   dist(α, C)² = ‖α‖² - (proj_C(α))²
  --   where proj_C(α) = max(0, max_ξ ⟨α, ξ⟩) · ξ_max
  --
  -- Key steps:
  -- 1. Show distToCone = Metric.infDist α (calibratedCone p x)
  -- 2. Use radial_minimization (already proven!) for each ray
  -- 3. Take supremum over all generators
  sorry
```

**Mathlib references:**
- `Mathlib.Analysis.InnerProductSpace.Projection` — projection onto subspaces
- `Mathlib.Topology.MetricSpace.HausdorffDistance` — `Metric.infDist`
- Use existing `radial_minimization` theorem in Grassmannian.lean

### 2.4 Wirtinger Inequality (1 axiom)

```lean
-- Cone.lean:78
axiom wirtinger_pairing_axiom (p : ℕ) (x : X) (ξ : SmoothForm n X (2 * p))
    (hξ : ξ ∈ simpleCalibratedForms p x) :
    pointwiseInner (omegaPow_point p x) ξ x = 1
```

**Mathematical content:** The Wirtinger inequality states that for a complex p-plane V:
$$\omega^p|_V = p! \cdot \text{vol}_V$$
With our normalization (ω^p/p! and unit volume forms), this gives pairing = 1.

**Proof strategy:**
```lean
theorem wirtinger_pairing_axiom (p : ℕ) (x : X) (ξ : SmoothForm n X (2 * p))
    (hξ : ξ ∈ simpleCalibratedForms p x) :
    pointwiseInner (omegaPow_point p x) ξ x = 1 := by
  -- ξ is the volume form of some complex p-plane V
  obtain ⟨V, hV_dim, hξ_eq⟩ := hξ
  rw [hξ_eq]
  -- omegaPow_point is ω^p / p! (check definition)
  -- The inner product ⟨ω^p/p!, vol_V⟩ at x evaluates to 1
  -- This is exactly the Wirtinger identity
  sorry
```

**This requires:** Definition of `omegaPow` to be compatible with Wirtinger.

### 2.5 Interior of Cone (1 axiom)

```lean
-- Cone.lean:105
axiom omegaPow_in_interior (p : ℕ) (x : X) :
    (omegaPow_point p x) ∈ interior (stronglyPositiveCone p x)
```

**Strategy:** Use finite-dimensional convex cone theory.

```lean
theorem omegaPow_in_interior (p : ℕ) (x : X) :
    (omegaPow_point p x) ∈ interior (stronglyPositiveCone p x) := by
  -- Key fact: ω^p pairs strictly positively with all simple calibrated forms
  have h_pos : ∀ ξ ∈ simpleCalibratedForms p x, pointwiseInner (omegaPow_point p x) ξ x > 0 := by
    intro ξ hξ
    rw [wirtinger_pairing_axiom p x ξ hξ]  -- = 1 > 0
    norm_num
  -- In finite dimensions, if a point pairs strictly positively with all generators
  -- of a convex cone, it lies in the interior
  -- Use: interior C = { y | ∀ ξ ∈ generators, ⟨y, ξ⟩ > 0 }
  sorry
```

**Mathlib references:**
- `Mathlib.Analysis.Convex.Cone.InnerDual` — dual cone characterization
- `Mathlib.Topology.Basic` — `interior_mem_nhds`

### 2.6 Uniform Radius (1 axiom)

```lean
-- Cone.lean:121
axiom exists_uniform_interior_radius [CompactSpace X] (p : ℕ) :
    ∃ r : ℝ, r > 0 ∧ ∀ x : X, ball (omegaPow_point p x) r ⊆ stronglyPositiveCone p x
```

**Strategy:** Use compactness and the already-proven `compact_pos_has_pos_inf`.

```lean
theorem exists_uniform_interior_radius [CompactSpace X] (p : ℕ) :
    ∃ r : ℝ, r > 0 ∧ ∀ x : X, ball (omegaPow_point p x) r ⊆ stronglyPositiveCone p x := by
  -- For each x, ω^p(x) is in the interior of the cone (by omegaPow_in_interior)
  -- So there exists r(x) > 0 with ball(ω^p(x), r(x)) ⊆ cone
  have h_local : ∀ x, ∃ r > 0, ball (omegaPow_point p x) r ⊆ stronglyPositiveCone p x := by
    intro x
    have h_int := omegaPow_in_interior p x
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h_int
    obtain ⟨r, hr_pos, hr_ball⟩ := h_int
    exact ⟨r, hr_pos, hr_ball⟩
  -- Define the radius function
  let radius_fun : X → ℝ := fun x => sSup { r | r > 0 ∧ ball (omegaPow_point p x) r ⊆ stronglyPositiveCone p x }
  -- This function is continuous (by variation of cone with x)
  have h_cont : Continuous radius_fun := sorry
  -- It's positive everywhere
  have h_pos : ∀ x, radius_fun x > 0 := sorry
  -- Use compact_pos_has_pos_inf (already proven!)
  exact compact_pos_has_pos_inf radius_fun h_cont h_pos
```

**Key insight:** The theorem `compact_pos_has_pos_inf` is already in Cone.lean!

---

## Track 2 Proof Order

1. **First:** Prove `simpleCalibratedForm_raw` (definition)
2. **Then:** Prove `coneDefect` (definition)
3. **Then:** Prove `wirtinger_pairing_axiom` (requires understanding of ω^p)
4. **Then:** Prove `dist_cone_sq_formula` (uses radial_minimization)
5. **Then:** Prove `omegaPow_in_interior` (uses wirtinger_pairing)
6. **Finally:** Prove `exists_uniform_interior_radius` (uses omegaPow_in_interior + compactness)

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

# Track 4: Sheaf Cohomology (FULL PROOF)

**File:** `Hodge/Classical/SerreVanishing.lean`
**Axioms:** 8
**Difficulty:** Very High — requires building sheaf theory infrastructure

## Overview

This is the hardest track. You need to build sheaf cohomology from scratch since Mathlib lacks this.
Split into 4 sub-tracks that can be worked on by different agents.

---

## Track 4A: Core Sheaf Types

**Axioms:** 2 | **Dependencies:** None | **Difficulty:** High

### 4A.1 Coherent Sheaf Definition

```lean
-- Line 16
axiom CoherentSheaf (n : ℕ) (X : Type u) [...] : Type u
```

**Strategy:** Define as a structure:

```lean
/-- A coherent sheaf on a complex manifold X. -/
structure CoherentSheaf (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] where
  /-- The stalk at each point is a finitely generated module over the local ring. -/
  Stalk : X → Type u
  stalk_module : ∀ x, Module ℂ (Stalk x)
  /-- Restriction maps between stalks (via germs). -/
  restriction : ∀ {U : Opens X} {x : X} (hx : x ∈ U), Stalk x
  /-- Local finite generation: covered by finitely many generators. -/
  locally_finitely_generated : ∀ x, ∃ (U : Opens X) (hx : x ∈ U) (n : ℕ)
    (gen : Fin n → (y : U) → Stalk y), ∀ y : U, ∀ s : Stalk y,
    ∃ (c : Fin n → ℂ), s = ∑ i, c i • gen i y
```

**Mathlib references:**
- `Mathlib.Topology.Sheaves.Sheaf` — general sheaf theory
- `Mathlib.Algebra.Category.ModuleCat.Basic` — module categories
- `Mathlib.Topology.Sheaves.SheafOfFunctions` — sheaves of functions

**Build command:** `lake build Hodge.Classical.SerreVanishing`

### 4A.2 Sheaf Cohomology Definition

```lean
-- Line 22
axiom SheafCohomology (F : CoherentSheaf n X) (q : ℕ) : Type u
```

**Strategy:** Use Čech cohomology (simpler than derived functors):

```lean
/-- Čech q-cochains on an open cover. -/
def CechCochain (F : CoherentSheaf n X) (U : ι → Opens X) (q : ℕ) :=
  (σ : Fin (q + 1) → ι) → F.Stalk (⋂ i, U (σ i))  -- sections over intersections

/-- The Čech differential d : C^q → C^{q+1}. -/
def cechDifferential (F : CoherentSheaf n X) (U : ι → Opens X) (q : ℕ) :
    CechCochain F U q →ₗ[ℂ] CechCochain F U (q + 1) := sorry

/-- Čech cohomology H^q(X, F) as kernel/image. -/
def SheafCohomology (F : CoherentSheaf n X) (q : ℕ) : Type u :=
  -- Take direct limit over all open covers
  -- H^q = ker(d^q) / im(d^{q-1})
  sorry
```

**Key insight:** For projective manifolds, Čech cohomology equals derived functor cohomology (Leray's theorem), so this approach is valid.

**Mathlib references:**
- `Mathlib.Algebra.Homology.Complex` — chain complexes
- `Mathlib.Algebra.Homology.Homology` — homology of complexes
- `Mathlib.CategoryTheory.Limits.Shapes.Kernels` — kernels and cokernels

---

## Track 4B: Algebraic Structure on Cohomology

**Axioms:** 2 | **Dependencies:** Track 4A | **Difficulty:** Medium

### 4B.1 AddCommGroup Instance

```lean
-- Line 28
axiom SheafCohomology.instAddCommGroup (F : CoherentSheaf n X) (q : ℕ) :
    AddCommGroup (SheafCohomology F q)
```

**Strategy:** Once `SheafCohomology` is defined as a quotient (kernel/image), the group structure is inherited:

```lean
instance SheafCohomology.instAddCommGroup (F : CoherentSheaf n X) (q : ℕ) :
    AddCommGroup (SheafCohomology F q) := by
  -- SheafCohomology F q = ker d^q / im d^{q-1}
  -- Quotient of AddCommGroup by AddSubgroup is AddCommGroup
  infer_instance  -- or use Submodule.Quotient.addCommGroup
```

**Mathlib references:**
- `Mathlib.LinearAlgebra.Quotient.Defs` — quotient modules
- `Submodule.Quotient.addCommGroup` — inherited group structure

### 4B.2 Module Instance

```lean
-- Line 35
axiom SheafCohomology.instModule (F : CoherentSheaf n X) (q : ℕ) :
    Module ℂ (SheafCohomology F q)
```

**Strategy:** Same as above — quotient of modules is a module:

```lean
instance SheafCohomology.instModule (F : CoherentSheaf n X) (q : ℕ) :
    Module ℂ (SheafCohomology F q) :=
  Submodule.Quotient.module _
```

---

## Track 4C: Sheaf Operations

**Axioms:** 2 | **Dependencies:** Track 4A | **Difficulty:** Medium

### 4C.1 Tensor Product with Line Bundle

```lean
-- Line 56
axiom tensorWithSheaf (L : HolomorphicLineBundle n X) (F : CoherentSheaf n X) :
    CoherentSheaf n X
```

**Strategy:** Define stalk-by-stalk:

```lean
def tensorWithSheaf (L : HolomorphicLineBundle n X) (F : CoherentSheaf n X) :
    CoherentSheaf n X where
  Stalk := fun x => L.Fiber x ⊗[ℂ] F.Stalk x
  stalk_module := fun x => inferInstance  -- tensor of modules is a module
  restriction := fun hx => sorry  -- tensor of restrictions
  locally_finitely_generated := fun x => by
    -- If F is locally generated by {s_i} and L is locally trivial,
    -- then L ⊗ F is locally generated by {e ⊗ s_i} where e is a local frame
    sorry
```

**Mathlib references:**
- `Mathlib.LinearAlgebra.TensorProduct.Basic` — tensor products
- `TensorProduct.instModule` — module structure on tensor

### 4C.2 Ideal Sheaf

```lean
-- Line 60
axiom idealSheaf (x : X) (k : ℕ) : CoherentSheaf n X
```

**Strategy:** The sheaf of germs of holomorphic functions vanishing to order ≥ k at x:

```lean
/-- The ideal sheaf m_x^k of functions vanishing to order k at x. -/
def idealSheaf (x₀ : X) (k : ℕ) : CoherentSheaf n X where
  Stalk := fun x =>
    if x = x₀ then
      -- At x₀: germs vanishing to order k
      { f : HolomorphicGerm x₀ // vanishingOrder f ≥ k }
    else
      -- Away from x₀: all germs (ideal is the whole ring)
      HolomorphicGerm x
  stalk_module := fun x => sorry
  restriction := fun hx => sorry
  locally_finitely_generated := fun x => by
    -- m_x^k is generated by z_1^{a_1} ... z_n^{a_n} with |a| = k
    -- in local coordinates
    sorry
```

**Mathlib references:**
- `Mathlib.RingTheory.Ideal.Basic` — ideal theory
- `Mathlib.RingTheory.PowerSeries.Basic` — power series (for vanishing order)

---

## Track 4D: Main Theorems

**Axioms:** 2 | **Dependencies:** Tracks 4A, 4B, 4C | **Difficulty:** Very High

### 4D.1 Serre Vanishing Theorem

```lean
-- Line 67
axiom serre_vanishing (L : HolomorphicLineBundle n X) [IsAmple L]
    (F : CoherentSheaf n X) (q : ℕ) (hq : q > 0) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, vanishes (tensorWithSheaf (L.power M) F) q
```

**This is a DEEP theorem.** Proof strategy:

1. **Setup:** Use Čech cohomology on a finite affine cover
2. **Key idea:** Ample line bundles have "enough sections" to kill cohomology
3. **Induction:** On the dimension of support of F

**Proof outline (following Hartshorne III.5):**

```lean
theorem serre_vanishing (L : HolomorphicLineBundle n X) [IsAmple L]
    (F : CoherentSheaf n X) (q : ℕ) (hq : q > 0) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, vanishes (tensorWithSheaf (L.power M) F) q := by
  -- Step 1: Reduce to the case where X is irreducible
  -- Step 2: Use that L^M is very ample for M large (Kodaira embedding)
  -- Step 3: Use the Leray spectral sequence for the embedding
  -- Step 4: Cohomology of coherent sheaves on projective space vanishes
  sorry
```

**Alternative:** If full proof is too hard, prove for specific cases:
- Case 1: F = O_X (structure sheaf) — this is Kodaira vanishing
- Case 2: F = ideal sheaf — needed for jet surjectivity

**References:**
- Hartshorne, "Algebraic Geometry", Chapter III, Theorem 5.2
- Serre, "Faisceaux algébriques cohérents" (FAC), 1955

### 4D.2 Jet Surjectivity Criterion

```lean
-- Line 75
axiom jet_surjectivity_criterion {L : HolomorphicLineBundle n X} {x : X} {k : ℕ} :
    vanishes (tensorWithSheaf L (idealSheaf x k)) 1 →
    Function.Surjective (jet_eval (L := L) x k)
```

**Strategy:** Use the long exact sequence in cohomology:

```lean
theorem jet_surjectivity_criterion {L : HolomorphicLineBundle n X} {x : X} {k : ℕ}
    (h : vanishes (tensorWithSheaf L (idealSheaf x k)) 1) :
    Function.Surjective (jet_eval (L := L) x k) := by
  -- Consider the short exact sequence of sheaves:
  -- 0 → L ⊗ m_x^{k+1} → L → L|_x / m_x^{k+1} → 0
  --
  -- Taking cohomology:
  -- H^0(X, L) → H^0(x, L_x / m_x^{k+1}) → H^1(X, L ⊗ m_x^{k+1})
  --     ↓              ↓                        ↓
  --  sections      k-jets at x              = 0 by hypothesis
  --
  -- If H^1 = 0, the map H^0 → jets is surjective.
  sorry
```

**Mathlib references:**
- `Mathlib.Algebra.Homology.ShortComplex.Exact` — exact sequences
- Long exact sequence machinery (may need to build)

---

## Track 4 Summary

| Sub-track | Axioms | Difficulty | Can Parallelize? |
|-----------|--------|------------|------------------|
| 4A: Core Types | 2 | High | Start here |
| 4B: Algebra | 2 | Medium | After 4A |
| 4C: Operations | 2 | Medium | After 4A |
| 4D: Theorems | 2 | Very High | After 4A,B,C |

**Recommended agent assignment:**
- Agent 1: Track 4A (core definitions)
- Agent 2: Track 4B + 4C (can work in parallel once 4A done)
- Agent 3: Track 4D (main theorems, needs all above)

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

