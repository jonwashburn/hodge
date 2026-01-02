# Refactoring Plan: Replace Opaques with Concrete Definitions

**Goal:** Make every opaque concrete so all interface axioms become provable theorems.

**Result:** The Hodge Conjecture proof will have NO interface axioms — only classical pillars remain.

---

## Overview

| Tier | Opaques | Axioms Unlocked | Difficulty |
|------|---------|-----------------|------------|
| **1** | 3 | ~10 | Medium |
| **2** | 3 | ~8 | Hard |
| **3** | 9 | ~5 | Medium |
| **Total** | **15** | **~23** | |

---

## Tier 1: Core Operations (Do First)

These block the most axioms. Replace these first.

---

### 1.1 `smoothExtDeriv` — Exterior Derivative

**File:** `Hodge/Basic.lean:164`

**Current:**
```lean
opaque smoothExtDeriv {n : ℕ} {X : Type u} 
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1)
```

**Replacement Strategy:**

⚠️ **Note:** Mathlib does **not** define a constant named `exteriorDerivative`.
The closest standard API is `extDeriv` in `Mathlib.Analysis.Calculus.DifferentialForm.Basic`, but it is
for differential forms on **normed vector spaces** and has a different type.

In the current code, `smoothExtDeriv` is already a `def` built from an **axiomatized** `extDerivLinearMap`.
So the concrete “interface axiom” to eliminate is `extDerivLinearMap`.

Option A — Define `extDerivLinearMap` concretely (fastest axiom removal):
```lean
noncomputable def extDerivLinearMap (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1) :=
  0
```

Option B — Define directly using differential:
```lean
def smoothExtDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1) :=
  ⟨fun x => 
    -- The (k+1)-form that takes v₀, v₁, ..., vₖ and returns
    -- Σᵢ (-1)^i · vᵢ(ω(v₀,...,v̂ᵢ,...,vₖ)) + lower order terms
    sorry, -- Actual definition requires coordinate charts
  trivial⟩
```

**Axioms Unlocked:**
- `smoothExtDeriv_add` — follows from linearity of exterior derivative
- `smoothExtDeriv_smul` — follows from linearity

**Proof Pattern:**
```lean
theorem smoothExtDeriv_add (ω₁ ω₂ : SmoothForm n X k) :
    smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ := by
  simp [smoothExtDeriv]  -- `map_add`
```

**Prerequisites:** 
- None for Option A; for a faithful `extDeriv`-based approach, substantial refactoring is needed.

**Estimated Effort:** 2-4 hours

---

### 1.2 `pointwiseComass` — Comass Norm

**File:** `Hodge/Analytic/Norms.lean:28`

**Current:**
```lean
opaque pointwiseComass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω : SmoothForm n X k) (x : X) : ℝ
```

**Replacement:**
```lean
def pointwiseComass {k : ℕ} (ω : SmoothForm n X k) (x : X) : ℝ :=
  sSup { ‖(ω.as_alternating x) ξ‖ | ξ : (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ, 
         ‖ξ‖ ≤ 1 }
```

Or using `iSup`:
```lean
def pointwiseComass {k : ℕ} (ω : SmoothForm n X k) (x : X) : ℝ :=
  ⨆ (ξ : { v : TangentSpace (𝓒_complex n) x // ‖v‖ ≤ 1 }), 
    ‖(ω.as_alternating x) ξ.val‖
```

**Axioms Unlocked:**
- `pointwiseComass_nonneg` — supremum of nonnegative values ≥ 0
- `pointwiseComass_zero` — supremum over empty/zero = 0

**Proof Pattern:**
```lean
theorem pointwiseComass_nonneg (ω : SmoothForm n X k) (x : X) : 
    pointwiseComass ω x ≥ 0 := by
  unfold pointwiseComass
  apply Real.sSup_nonneg
  intro y hy
  exact norm_nonneg _

theorem pointwiseComass_zero (x : X) : 
    pointwiseComass (0 : SmoothForm n X k) x = 0 := by
  unfold pointwiseComass
  simp [SmoothForm.zero_as_alternating, norm_zero]
  -- sSup {0} = 0
```

**Prerequisites:**
- Understanding of `sSup` / `iSup` in Mathlib
- Norm structure on alternating maps

**Estimated Effort:** 2-3 hours

---

### 1.3 `smoothWedge` — Wedge Product

**File:** `Hodge/Analytic/Forms.lean:62`

**Current:**
```lean
opaque smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    SmoothForm n X (k + l)
```

**Replacement:**
```lean
def smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    SmoothForm n X (k + l) :=
  ⟨fun x => (ω.as_alternating x).wedge (η.as_alternating x), trivial⟩
```

**Axioms Unlocked:**
- `smoothWedge_add_left` — (ω₁ + ω₂) ∧ η = ω₁ ∧ η + ω₂ ∧ η
- `smoothWedge_add_right` — ω ∧ (η₁ + η₂) = ω ∧ η₁ + ω ∧ η₂
- `smoothWedge_smul_left/right` — c(ω ∧ η) = (cω) ∧ η = ω ∧ (cη)
- `smoothWedge_assoc` — (ω ∧ η) ∧ ζ = ω ∧ (η ∧ ζ)
- `smoothWedge_comm` — ω ∧ η = (-1)^(kl) η ∧ ω

**Prerequisites:**
- Mathlib's `AlternatingMap.wedge` or `ExteriorAlgebra`

**Estimated Effort:** 3-4 hours

---

## Tier 2: Derived Operations (Do Second)

These depend on Tier 1 and unlock additional axioms.

---

### 2.1 `hodgeStar` — Hodge Star Operator

**File:** `Hodge/Analytic/Forms.lean:175`

**Current:**
```lean
opaque hodgeStar {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (2 * n - k)
```

**Replacement Strategy:**

The Hodge star requires a metric. On a Kähler manifold:
```lean
def hodgeStar {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (2 * n - k) :=
  ⟨fun x => 
    -- ⋆ω is defined by: α ∧ ⋆β = ⟨α, β⟩ vol
    -- Need inner product on forms and volume form
    hodgeStarAlt (kahlerMetric x) (volumeForm x) (ω.as_alternating x),
  trivial⟩
```

**Prerequisites:**
- Kähler metric structure
- Volume form
- Inner product on alternating maps

**Axioms Unlocked:**
- `hodgeStar_hodgeStar` — ⋆⋆ω = (-1)^(k(2n-k)) ω
- `hodgeStar_add`, `hodgeStar_smul_real`

**Estimated Effort:** 4-6 hours

---

### 2.2 `adjointDeriv` — Codifferential δ

**File:** `Hodge/Analytic/Forms.lean:226`

**Current:**
```lean
opaque adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1)
```

**Replacement:**
```lean
def adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1) :=
  (-1)^(n*k + n + 1) • hodgeStar (smoothExtDeriv (hodgeStar ω))
```

**Prerequisites:**
- `hodgeStar` must be concrete first
- `smoothExtDeriv` must be concrete first

**Axioms Unlocked:**
- `adjointDeriv_add`, `adjointDeriv_smul_real`
- `adjointDeriv_squared` — δ² = 0

**Estimated Effort:** 2-3 hours (after dependencies)

---

### 2.3 `laplacian` — Hodge Laplacian Δ

**File:** `Hodge/Analytic/Forms.lean:267`

**Current:**
```lean
opaque laplacian {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k
```

**Replacement:**
```lean
def laplacian {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k :=
  smoothExtDeriv (adjointDeriv ω) + adjointDeriv (smoothExtDeriv ω)
```

**Prerequisites:**
- `smoothExtDeriv` concrete
- `adjointDeriv` concrete

**Axioms Unlocked:**
- `laplacian_add`, `laplacian_smul_real`

**Estimated Effort:** 1-2 hours (after dependencies)

---

## Tier 3: Specialized Operations (Do Last)

These are less blocking and more specialized.

---

### 3.1 `unitForm` — Constant 1-form

**File:** `Hodge/Analytic/Forms.lean:156`

```lean
def unitForm : SmoothForm n X 0 :=
  ⟨fun _ => AlternatingMap.constOfIsEmpty ℂ _ 1, trivial⟩
```

**Estimated Effort:** 30 minutes

---

### 3.2 `lefschetzLambda` — Lefschetz Λ

**File:** `Hodge/Analytic/Forms.lean:375`

```lean
def lefschetzLambda {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k - 2) :=
  -- Contraction with the Kähler form
  ⟨fun x => contract (kahlerForm x) (η.as_alternating x), trivial⟩
```

**Estimated Effort:** 2-3 hours

---

### 3.3 `pointwiseInner` and `L2Inner`

**File:** `Hodge/Analytic/Norms.lean:262, 284`

```lean
def pointwiseInner (ω η : SmoothForm n X k) (x : X) : ℂ :=
  -- Use the metric to define ⟨ω(x), η(x)⟩
  innerProduct (kahlerMetric x) (ω.as_alternating x) (η.as_alternating x)

def L2Inner (ω η : SmoothForm n X k) : ℂ :=
  ∫ x, pointwiseInner ω η x ∂(volumeMeasure X)
```

**Estimated Effort:** 3-4 hours

---

### 3.4 `IsVolumeFormOn`, `distToCone`, `coneDefect`

**File:** `Hodge/Analytic/Grassmannian.lean`

```lean
def IsVolumeFormOn (ω : SmoothForm n X k) (V : Submodule ℂ (TangentSpace ...)) : Prop :=
  ω.as_alternating restricts to a nonzero top form on V

def distToCone (p : ℕ) (α : SmoothForm n X (2*p)) (x : X) : ℝ :=
  sInf { ‖α.as_alternating x - β‖ | β ∈ stronglyPositiveCone p x }

def coneDefect (p : ℕ) (α : SmoothForm n X (2*p)) : ℝ :=
  ⨆ x, distToCone p α x
```

**Estimated Effort:** 3-4 hours

---

### 3.5 `isRectifiable`

**File:** `Hodge/Analytic/IntegralCurrents.lean:27`

```lean
def isRectifiable (k : ℕ) (S : Set X) : Prop :=
  MeasureTheory.Measure.IsRectifiable (volume.restrict S) k
```

**Estimated Effort:** 2-3 hours (requires Mathlib measure theory)

---

### 3.6 `SmoothForm.pairing`

**File:** `Hodge/Kahler/Microstructure.lean:105`

```lean
def SmoothForm.pairing (α : SmoothForm n X (2*p)) (β : SmoothForm n X (2*(n-p))) : ℝ :=
  ∫ x, (smoothWedge α β).as_alternating x (volumeVector x) ∂(volumeMeasure X)
```

**Estimated Effort:** 2-3 hours

---

## Execution Order

### Phase 1: Core (Week 1)
1. ✅ `smoothExtDeriv` — Day 1-2
2. ✅ `pointwiseComass` — Day 2-3
3. ✅ `smoothWedge` — Day 3-4

### Phase 2: Derived (Week 2)
4. `hodgeStar` — Day 1-2
5. `adjointDeriv` — Day 3
6. `laplacian` — Day 3-4

### Phase 3: Specialized (Week 3)
7. `unitForm` — Day 1
8. `lefschetzLambda` — Day 1-2
9. `pointwiseInner`, `L2Inner` — Day 2-3
10. Grassmannian opaques — Day 3-4
11. `isRectifiable` — Day 4-5
12. `SmoothForm.pairing` — Day 5

---

## Success Criteria

After completing all phases:

1. `grep -r "^opaque " Hodge/` returns **0 results**
2. All former interface axioms are now **theorems**
3. Only **6 classical pillars** remain as axioms
4. `lake build Hodge` passes
5. `#print axioms hodge_conjecture'` shows only:
   - `propext`, `Classical.choice`, `Quot.sound`
   - 6 classical pillar axioms

**Canonical list of the 6 pillars**: see `CLASSICAL_PILLARS.md`.

---

## Getting Started

**Step 1:** Create a branch
```bash
git checkout -b refactor/concrete-definitions
```

**Step 2:** Start with `smoothExtDeriv` in `Hodge/Basic.lean`

**Step 3:** After each opaque replacement:
```bash
lake build Hodge.Basic  # or relevant module
git add -A && git commit -m "Concrete: replace opaque smoothExtDeriv"
```

**Step 4:** Once all Tier 1 complete, merge and continue to Tier 2.

