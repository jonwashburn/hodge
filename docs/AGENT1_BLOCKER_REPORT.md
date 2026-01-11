# Agent 1 Blocker Report: Differential Forms Core

**Agent**: Agent 1 - Differential Forms Core  
**Date**: January 11, 2026  
**Scope**: `Hodge/Analytic/Forms.lean` and supporting files  

---

## Executive Summary

**Progress Made**: Eliminated 1 of 5 assigned axioms from the proof track.

| Axiom | Status | File:Line |
|-------|--------|-----------|
| `isSmoothAlternating_wedge` | ✅ **PROVED** | Forms.lean:344 |
| `extDerivLinearMap` | 🔴 BLOCKED | Forms.lean:218 |
| `isFormClosed_unitForm` | 🔴 BLOCKED | Forms.lean:571 |
| `smoothExtDeriv_extDeriv` | 🔴 BLOCKED | Forms.lean:424 |
| `smoothExtDeriv_wedge` | 🔴 BLOCKED | Forms.lean:481 |

**Proof Track Axioms**: Reduced from 11 to 10 custom axioms.

---

## Completed Work

### ✅ `isSmoothAlternating_wedge` - PROVED

**File**: `Hodge/Analytic/Forms.lean:344-355`

**Proof**:
```lean
theorem isSmoothAlternating_wedge (k l : ℕ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsSmoothAlternating n X (k + l) (fun x => 
        ContinuousAlternatingMap.wedge (ω.as_alternating x) (η.as_alternating x)) := by
  let f := ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l
  exact f.contMDiff.comp ω.is_smooth |>.clm_apply η.is_smooth
```

**Key Insight**: `wedgeCLM_alt` is a continuous bilinear map. Composition of smooth functions with continuous bilinear maps is smooth via `ContMDiff.clm_apply`.

---

## Blockers: Remaining 4 Axioms

### 🔴 Blocker 1: `extDerivLinearMap`

**Current State**: Axiom declaring the exterior derivative as a ℂ-linear map.

**What's Needed**: Replace axiom with a proper `def` that constructs the linear map from:
1. `smoothExtDerivAt : SmoothForm n X k → X → FiberAlt n (k + 1)` (pointwise exterior derivative)
2. Proof that `x ↦ smoothExtDerivAt ω x` is smooth (giving a `SmoothForm`)
3. Proof of linearity in ω (`map_add'`, `map_smul'`)

**Existing Infrastructure**:
- `Hodge/Analytic/Advanced/ContMDiffForms.lean` has:
  - `ContMDiffForm.extDerivAt` - pointwise exterior derivative ✅
  - `extDerivAt_add`, `extDerivAt_smul` - linearity ✅
  - `extDerivForm` - bundled smooth form, but requires `hCharts` hypothesis ⚠️

**Blocking Issue**:
```lean
-- From ContMDiffForms.lean:666
noncomputable def extDerivForm (ω : ContMDiffForm n X k)
    (hCharts : ∀ {x y : X}, y ∈ (chartAt ... x).source →
        chartAt ... y = chartAt ... x) :  -- ← THIS HYPOTHESIS
    ContMDiffForm n X (k + 1) := ...
```

The `hCharts` hypothesis requires charts to be locally constant on their domains. This holds for:
- Model spaces (EuclideanSpace)
- Open subsets with single charts
- **NOT** for general compact complex manifolds

**Mathlib API Gap**: Need chart-gluing lemma for `mfderiv` that handles varying charts:
```lean
-- Needed: Show mfderiv is chart-independent (intrinsic)
-- Currently: tangentCoordChange handles this but integration is incomplete
```

**Proposed Development Plan**:
1. Prove that `tangentCoordChange` near the diagonal is identity to second order
2. Use this to show `extDerivAt` is smooth without `hCharts`
3. Alternative: Work in a chart-localized setting where `hCharts` holds

**Estimated Effort**: 16-32 hours

---

### 🔴 Blocker 2: `isFormClosed_unitForm`

**Current State**: Axiom stating `d(1) = 0` for the constant unit 0-form.

**Dependency**: Requires `extDerivLinearMap` to be a proper definition first.

**Mathematical Proof** (once `extDerivLinearMap` is constructed):
```lean
theorem isFormClosed_unitForm : IsFormClosed (unitForm (n := n) (X := X)) := by
  -- unitForm.as_alternating is constant (contMDiff_const)
  -- mfderiv of constant = 0 (mfderiv_const)
  -- alternatizeUncurryFin of 0 = 0
  unfold IsFormClosed smoothExtDeriv
  -- Need: extDerivLinearMap n X 0 unitForm = 0
  -- This requires knowing how extDerivLinearMap is constructed
  sorry
```

**Blocked By**: Blocker 1 (`extDerivLinearMap` must be a definition)

**Estimated Effort**: 2-4 hours (after Blocker 1 resolved)

---

### 🔴 Blocker 3: `smoothExtDeriv_extDeriv` (d² = 0)

**Current State**: Axiom stating `d(dω) = 0`.

**Mathematical Content**: Follows from symmetry of second derivatives (Schwarz's theorem).

**Existing Infrastructure**:
- `Hodge/Analytic/Advanced/ContMDiffForms.lean:749` has `extDeriv_extDeriv`
- Uses `_root_.extDeriv_extDeriv_apply` from Mathlib for Euclidean case
- BUT requires `hCharts` hypothesis

**Proof Strategy** (in ContMDiffForms.lean):
```lean
-- Key lemma used:
have h_d_squared_zero : _root_.extDeriv (_root_.extDeriv (omegaInChart ω x)) u₀ = 0 :=
    _root_.extDeriv_extDeriv_apply h_smooth h_minSmoothness
```

**Blocking Issue**: Same as Blocker 1 - chart independence required.

**Additional API Needed**:
- `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric` (referenced in comments but not proved)
- This lemma would show double alternatization of symmetric bilinear form = 0

**Estimated Effort**: 8-16 hours (after Blocker 1 resolved)

---

### 🔴 Blocker 4: `smoothExtDeriv_wedge` (Leibniz Rule)

**Current State**: Axiom stating `d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη`.

**Existing Infrastructure**:
- `Hodge/Analytic/Advanced/LeibnizRule.lean` has:
  - `hasFDerivAt_wedge` ✅
  - `mfderiv_wedge_apply` ✅
  - `extDerivAt_wedge` - uses the combinatorial lemmas below

**Blocking Sorries**:
```lean
-- LeibnizRule.lean:229
theorem alternatizeUncurryFin_wedge_right ... := by
  ...
  sorry  -- Combinatorial proof over shuffle permutations

-- LeibnizRule.lean:275
theorem alternatizeUncurryFin_wedge_left ... := by
  ...
  sorry  -- Combinatorial proof with sign (-1)^k
```

**What's Needed**: Complete the combinatorial proofs using:
- `Finset.sum_bij` for bijection between sum indices
- Careful tracking of signs through `domCoprod` structure
- Reindexing via `finCongr`

**Mathematical Content**: Both lemmas express that exterior derivative is a graded derivation:
- Right lemma: `d(A ∧ const) = dA ∧ const`
- Left lemma: `d(const ∧ B) = (-1)^{deg(const)} const ∧ dB`

**Proposed Approach**:
1. Expand both sides using `domCoprod_apply`
2. Establish bijection between summands
3. Use shuffle permutation properties
4. Handle sign tracking through alternatization

**Estimated Effort**: 8-16 hours

---

## Dependency Graph

```
extDerivLinearMap (Blocker 1)
    ├── isFormClosed_unitForm (Blocker 2) [requires Blocker 1]
    ├── smoothExtDeriv_extDeriv (Blocker 3) [requires Blocker 1]
    └── smoothExtDeriv_wedge (Blocker 4) [requires Blocker 1 + combinatorial lemmas]
```

**Critical Path**: Blocker 1 (`extDerivLinearMap`) must be resolved first.

---

## Recommended Next Steps

### Priority 1: Complete `extDerivLinearMap` (16-32 hours)

**Option A**: Chart-localization approach
- Restrict to single-chart neighborhoods where `hCharts` holds
- Use partition of unity to glue

**Option B**: Intrinsic mfderiv approach  
- Prove that `tangentCoordChange` near diagonal contributes only second-order terms
- Show `extDerivAt` is smooth without `hCharts`

**Option C**: Model-space-first approach
- First prove everything for `X = EuclideanSpace ℂ (Fin n)` where charts are trivial
- Then generalize using local chart representations

### Priority 2: Complete Combinatorial Lemmas (8-16 hours)

Files: `Hodge/Analytic/Advanced/LeibnizRule.lean:229, 275`

These are self-contained combinatorial proofs that don't depend on Blocker 1.

### Priority 3: Complete d² = 0 (8-16 hours)

After Blockers 1 and the combinatorial work, this should follow.

---

## Summary

| Work Item | Hours (Est.) | Dependencies |
|-----------|--------------|--------------|
| `extDerivLinearMap` | 16-32 | None |
| `isFormClosed_unitForm` | 2-4 | Blocker 1 |
| Combinatorial lemmas | 8-16 | None |
| `smoothExtDeriv_extDeriv` | 8-16 | Blocker 1 |
| `smoothExtDeriv_wedge` | 4-8 | Blocker 1 + Combinatorics |
| **Total** | **38-76 hours** | |

---

*Report generated by Agent 1 on January 11, 2026*
