# Agent Assignments: Tier 1 Refactoring — Replace Opaques

**Mission:** Replace opaque definitions with concrete implementations to eliminate interface axioms.

**Goal:** Make the Hodge proof unconditional — only classical pillars remain as axioms.

---

## ⚠️ CRITICAL RULES

1. **TEST LOCALLY**: `lake build Hodge.Basic` (or relevant module) before commit
2. **ONE OPAQUE AT A TIME**: Replace, prove axioms, commit, then next
3. **IF STUCK → ASK**: Don't leave broken code

---

## Current Status

| Metric | Count |
|--------|-------|
| Opaques remaining | 15 |
| Interface axioms (blocked) | ~9 |
| Classical pillars (keep) | 6 |
| Target after refactor | **6 axioms only** |

---

## Tier 1: Core Operations (This Round)

These 3 opaques block the most axioms. Replace them first.

---

# 🔷 AGENT 1: `smoothExtDeriv` — Exterior Derivative

**File:** `Hodge/Basic.lean:164`

**Task:** Replace opaque with concrete definition using Mathlib.

**Current (opaque):**
```lean
opaque smoothExtDeriv {n : ℕ} {X : Type u} 
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1)
```

**Replacement (concrete):**
```lean
import Mathlib.Geometry.Manifold.DerivationBundle

def smoothExtDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1) :=
  ⟨fun x => exteriorDerivative ℂ (ω.as_alternating x), trivial⟩
```

**Then prove these axioms as theorems:**
```lean
theorem smoothExtDeriv_add (ω₁ ω₂ : SmoothForm n X k) :
    smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ := by
  ext x
  simp [smoothExtDeriv, SmoothForm.add_as_alternating]
  -- Use linearity of exteriorDerivative

theorem smoothExtDeriv_smul (c : ℂ) (ω : SmoothForm n X k) :
    smoothExtDeriv (c • ω) = c • smoothExtDeriv ω := by
  ext x
  simp [smoothExtDeriv]
  -- Use linearity of exteriorDerivative
```

**Verification:**
```bash
lake build Hodge.Basic
```

---

# 🔷 AGENT 2: `pointwiseComass` — Comass Norm

**File:** `Hodge/Analytic/Norms.lean:28`

**Task:** Replace opaque with concrete supremum definition.

**Current (opaque):**
```lean
opaque pointwiseComass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω : SmoothForm n X k) (x : X) : ℝ
```

**Replacement (concrete):**
```lean
noncomputable def pointwiseComass {k : ℕ} (ω : SmoothForm n X k) (x : X) : ℝ :=
  sSup { ‖(ω.as_alternating x) v‖ | (v : _), ‖v‖ ≤ 1 }
```

Or simpler if bounded:
```lean
noncomputable def pointwiseComass {k : ℕ} (ω : SmoothForm n X k) (x : X) : ℝ :=
  ‖ω.as_alternating x‖  -- operator norm
```

**Then prove these axioms as theorems:**
```lean
theorem pointwiseComass_nonneg (ω : SmoothForm n X k) (x : X) : 
    pointwiseComass ω x ≥ 0 := by
  unfold pointwiseComass
  exact norm_nonneg _  -- or sSup of nonneg

theorem pointwiseComass_zero (x : X) : 
    pointwiseComass (0 : SmoothForm n X k) x = 0 := by
  unfold pointwiseComass
  simp [SmoothForm.zero_as_alternating]
```

**Verification:**
```bash
lake build Hodge.Analytic.Norms
```

---

# 🔷 AGENT 3: `smoothWedge` — Wedge Product

**File:** `Hodge/Analytic/Forms.lean:62`

**Task:** Replace opaque with concrete wedge product.

**Current (opaque):**
```lean
opaque smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    SmoothForm n X (k + l)
```

**Replacement (concrete):**
```lean
def smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    SmoothForm n X (k + l) :=
  ⟨fun x => AlternatingMap.wedge (ω.as_alternating x) (η.as_alternating x), trivial⟩
```

**Then prove these axioms as theorems:**
```lean
theorem smoothWedge_add_left (ω₁ ω₂ : SmoothForm n X k) (η : SmoothForm n X l) :
    smoothWedge (ω₁ + ω₂) η = smoothWedge ω₁ η + smoothWedge ω₂ η := by
  ext x
  simp [smoothWedge]
  exact AlternatingMap.wedge_add_left _ _ _

theorem smoothWedge_add_right (ω : SmoothForm n X k) (η₁ η₂ : SmoothForm n X l) :
    smoothWedge ω (η₁ + η₂) = smoothWedge ω η₁ + smoothWedge ω η₂ := by
  ext x
  simp [smoothWedge]
  exact AlternatingMap.wedge_add_right _ _ _
```

**Verification:**
```bash
lake build Hodge.Analytic.Forms
```

---

# 🔷 AGENTS 4-8: Support & Remaining Axioms

While Tier 1 is in progress, continue working on:

| Agent | Task |
|-------|------|
| **4** | Help Agent 1 or work on `smoothExtDeriv` tests |
| **5** | Help Agent 2 or work on `comass` helper lemmas |
| **6** | Work on remaining Hodge-Weight axioms |
| **7** | Work on remaining Hodge-Weight axioms |
| **8** | Document classical pillars |

---

## Remaining Hodge-Weight Axioms (parallel work)

| Axiom | File | Status |
|-------|------|--------|
| `omega_pow_represents_multiple` | Main.lean | May be classical pillar |
| `omegaPow_in_interior` | Cone.lean | Needs Wirtinger |
| `wirtinger_comass_bound` | Calibration.lean | Classical result |
| `simpleCalibratedForm` | Grassmannian.lean | Volume form |
| `conePositive_comass_bound` | Microstructure.lean | Uniform bound |

---

## Success Criteria for Tier 1

After Tier 1 complete:
- [ ] `smoothExtDeriv` is a `def`, not `opaque`
- [ ] `pointwiseComass` is a `def`, not `opaque`
- [ ] `smoothWedge` is a `def`, not `opaque`
- [ ] `smoothExtDeriv_add/smul` are theorems, not axioms
- [ ] `pointwiseComass_nonneg/zero` are theorems, not axioms
- [ ] `smoothWedge_add_left/right` are theorems, not axioms
- [ ] `lake build Hodge` passes

---

## Workflow

```bash
# 1. Pull latest
git pull origin main

# 2. Work on your assigned opaque
# 3. Test the specific module
lake build Hodge.Basic  # or Hodge.Analytic.Norms, etc.

# 4. If it passes, commit
git add -A && git commit -m "Agent N: Concrete smoothExtDeriv" && git push

# 5. If blocked, ask for help
```

---

## Reference

See `REFACTORING_PLAN.md` for:
- Full list of all 15 opaques
- Tier 2 and Tier 3 plans
- Detailed replacement strategies
