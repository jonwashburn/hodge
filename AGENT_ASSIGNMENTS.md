# Agent Assignments: Tier 1 Progress + Rebalanced

**Progress:** 15 → 13 opaques (2 made concrete!)

---

## ✅ COMPLETED THIS ROUND

| Opaque | Status | Agent |
|--------|--------|-------|
| `smoothExtDeriv` | ✅ **NOW DEF** | 1 |
| `pointwiseComass` | ✅ **NOW DEF** | 2 |

**Great work! 2 core opaques converted to concrete definitions.**

---

## Remaining Opaques (13)

| # | Opaque | File | Tier |
|---|--------|------|------|
| 1 | `smoothWedge` | Forms.lean | **1** |
| 2 | `unitForm` | Forms.lean | 3 |
| 3 | `hodgeStar` | Forms.lean | 2 |
| 4 | `adjointDeriv` | Forms.lean | 2 |
| 5 | `laplacian` | Forms.lean | 2 |
| 6 | `lefschetzLambda` | Forms.lean | 3 |
| 7 | `pointwiseInner` | Norms.lean | 3 |
| 8 | `L2Inner` | Norms.lean | 3 |
| 9 | `IsVolumeFormOn` | Grassmannian.lean | 3 |
| 10 | `distToCone` | Grassmannian.lean | 3 |
| 11 | `coneDefect` | Grassmannian.lean | 3 |
| 12 | `isRectifiable` | IntegralCurrents.lean | 3 |
| 13 | `SmoothForm.pairing` | Microstructure.lean | 3 |

---

## ⚠️ RULES

1. **TEST**: `lake build Hodge.Analytic.Forms` (or relevant module)
2. **ONE OPAQUE AT A TIME**
3. **IF STUCK → ASK**

---

# Rebalanced Assignments

## 🔷 AGENT 1: Complete Tier 1

**Remaining:** `smoothWedge`

**File:** `Hodge/Analytic/Forms.lean:58`

```lean
-- Replace:
opaque smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    SmoothForm n X (k + l)

-- With:
def smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    SmoothForm n X (k + l) :=
  ⟨fun x => AlternatingMap.wedge (ω.as_alternating x) (η.as_alternating x), trivial⟩
```

---

## 🔷 AGENT 2: Tier 2 — `hodgeStar`

**File:** `Hodge/Analytic/Forms.lean:171`

```lean
-- Hodge star needs metric structure
-- Define: ⋆ω where α ∧ ⋆β = ⟨α, β⟩ vol
def hodgeStar {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (2 * n - k) :=
  ⟨fun x => hodgeStarAlt (metric x) (ω.as_alternating x), trivial⟩
```

---

## 🔷 AGENT 3: Tier 2 — `adjointDeriv`

**File:** `Hodge/Analytic/Forms.lean:222`

**Depends on:** `hodgeStar` (Agent 2) + `smoothExtDeriv` (✅ done)

```lean
def adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1) :=
  (-1)^(n*k + n + 1) • hodgeStar (smoothExtDeriv (hodgeStar ω))
```

---

## 🔷 AGENT 4: Tier 2 — `laplacian`

**File:** `Hodge/Analytic/Forms.lean:263`

**Depends on:** `adjointDeriv` (Agent 3) + `smoothExtDeriv` (✅ done)

```lean
def laplacian {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k :=
  smoothExtDeriv (adjointDeriv ω) + adjointDeriv (smoothExtDeriv ω)
```

---

## 🔷 AGENT 5: Tier 3 — `unitForm` + `lefschetzLambda`

**Files:** `Hodge/Analytic/Forms.lean`

```lean
def unitForm : SmoothForm n X 0 :=
  ⟨fun _ => AlternatingMap.constOfIsEmpty ℂ _ 1, trivial⟩

def lefschetzLambda {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k - 2) :=
  ⟨fun x => contract (kahlerForm x) (η.as_alternating x), trivial⟩
```

---

## 🔷 AGENT 6: Tier 3 — `pointwiseInner` + `L2Inner`

**File:** `Hodge/Analytic/Norms.lean`

```lean
def pointwiseInner (ω η : SmoothForm n X k) (x : X) : ℂ :=
  innerProduct (metric x) (ω.as_alternating x) (η.as_alternating x)

def L2Inner (ω η : SmoothForm n X k) : ℂ :=
  ∫ x, pointwiseInner ω η x ∂(volumeMeasure X)
```

---

## 🔷 AGENT 7: Tier 3 — Grassmannian opaques

**File:** `Hodge/Analytic/Grassmannian.lean`

```lean
def IsVolumeFormOn (ω : SmoothForm n X k) (V : Submodule) : Prop :=
  ω restricts to nonzero top form on V

def distToCone (p : ℕ) (α : SmoothForm n X (2*p)) (x : X) : ℝ :=
  sInf { ‖α.as_alternating x - β‖ | β ∈ positiveCone p x }

def coneDefect (p : ℕ) (α : SmoothForm n X (2*p)) : ℝ :=
  ⨆ x, distToCone p α x
```

---

## 🔷 AGENT 8: Tier 3 — `isRectifiable` + `SmoothForm.pairing`

**Files:** `IntegralCurrents.lean`, `Microstructure.lean`

```lean
def isRectifiable (k : ℕ) (S : Set X) : Prop :=
  MeasureTheory.Measure.IsRectifiable (volume.restrict S) k

def SmoothForm.pairing (α : SmoothForm n X (2*p)) (β : SmoothForm n X (2*(n-p))) : ℝ :=
  ∫ x, (smoothWedge α β).as_alternating x (volumeVector x) ∂μ
```

---

## Summary

| Agent | Task | Tier | Depends On |
|-------|------|------|------------|
| 1 | `smoothWedge` | 1 | — |
| 2 | `hodgeStar` | 2 | — |
| 3 | `adjointDeriv` | 2 | Agent 2 |
| 4 | `laplacian` | 2 | Agent 3 |
| 5 | `unitForm`, `lefschetzLambda` | 3 | — |
| 6 | `pointwiseInner`, `L2Inner` | 3 | — |
| 7 | Grassmannian opaques | 3 | — |
| 8 | `isRectifiable`, `pairing` | 3 | Agent 1 |

---

## Target

| Metric | Before | After Tier 1 | Target |
|--------|--------|--------------|--------|
| Opaques | 15 | 13 | **0** |
| Interface axioms | ~9 | ~7 | **0** |
| Classical pillars | 6 | 6 | 6 |

---

## Verification

```bash
# Test specific module
lake build Hodge.Analytic.Forms

# Count remaining opaques
grep -rn "^opaque " Hodge/ --include="*.lean" | wc -l
```
