# Agent Assignments: 30 Axioms → 8 Agents

**Mission:** Prove all 30 axioms in `hodge_conjecture'` proof chain.

**Progress:** 44 → 35 → 32 → 30 axioms

**Verification:** `lake env lean DependencyCheck.lean` confirms all 30 are in proof chain.

---

## 🚫 RULES

1. **NO `sorry`, `admit`, `trivial`, `native_decide`**
2. **NO stub definitions** (e.g., `def mass := 0`)
3. **Build passes:** `lake build Hodge`
4. **Verify:** Axiom removed from `DependencyCheck.lean` output

---

## Axiom Classification

### 🔴 CLASSICAL PILLARS (Acceptable as Axioms) — 6 axioms
Deep theorems from the literature. These are acceptable final axioms:

| Axiom | Description | Reference |
|-------|-------------|-----------|
| `serre_gaga` | Algebraic = analytic on projective | Serre 1956 |
| `flat_limit_existence` | Federer-Fleming compactness | FF 1960 |
| `mass_lsc` | Lower semicontinuity of mass | Federer 1969 |
| `calibration_defect_from_gluing` | GMT gluing estimate | FF 1960 |
| `harvey_lawson_fundamental_class` | HL fundamental class | HL 1983 |
| `lefschetz_lift_signed_cycle` | Lefschetz on cycles | Hard Lefschetz |

### 🟡 INTERFACE AXIOMS (Opaque Type Structure) — 8 axioms
These define algebraic structure on opaque types. May be provable via architecture change:

| Axiom | Type | Strategy |
|-------|------|----------|
| `isSmoothAlternating_zero` | SmoothForm | Define predicate constructively |
| `isSmoothAlternating_add` | SmoothForm | Define predicate constructively |
| `isSmoothAlternating_neg` | SmoothForm | Define predicate constructively |
| `isSmoothAlternating_smul` | SmoothForm | Define predicate constructively |
| `isSmoothAlternating_sub` | SmoothForm | Define predicate constructively |
| `SmoothForm.instTopologicalSpace` | SmoothForm | Use Mathlib topology |
| `smoothExtDeriv_add` | Derivative | Follows from linearity if d is defined |
| `smoothExtDeriv_smul` | Derivative | Follows from linearity if d is defined |

### 🟢 HODGE-WEIGHT AXIOMS (Must Prove) — 16 axioms
These carry mathematical substance for the Hodge conjecture:

| Axiom | Hodge Weight | Why It Matters |
|-------|--------------|----------------|
| `omega_pow_IsFormClosed` | **HIGH** | d(ω^p) = 0 for Kähler form |
| `omega_pow_is_rational` | **HIGH** | [ω^p] ∈ H(X,ℚ) |
| `omega_pow_represents_multiple` | **HIGH** | Key algebraicity claim |
| `omegaPow_in_interior` | **HIGH** | ω^p in cone interior |
| `shift_makes_conePositive_rat` | **HIGH** | Rational shift into cone |
| `wirtinger_comass_bound` | **HIGH** | Wirtinger inequality |
| `simpleCalibratedForm` | **MEDIUM** | Volume form calibration |
| `pointwiseComass_nonneg` | **MEDIUM** | Comass ≥ 0 |
| `pointwiseComass_zero` | **MEDIUM** | Comass(0) = 0 |
| `conePositive_comass_bound` | **MEDIUM** | Uniform comass bound |
| `eval_le_mass` | **MEDIUM** | T(ψ) ≤ mass·comass |
| `flatNorm_boundary_le` | **MEDIUM** | ‖∂T‖_flat ≤ ‖T‖_flat |
| `flatNorm_eq_zero_iff` | **MEDIUM** | ‖T‖ = 0 ↔ T = 0 |
| `smoothExtDeriv_smul_real` | **LOW** | d(r·ω) = r·dω |
| `ofForm_smul_real` | **LOW** | [r·ω] = r·[ω] |
| `RawSheetSum.toIntegralCurrent_toFun_eq_zero` | **LOW** | Technical cast |

---

## ✅ Recently Proved (Round 15)

| Axiom | Now | Prover |
|-------|-----|--------|
| `mass` | def (supremum) | Agent 4 |
| `mass_nonneg` | theorem | Agent 4 |
| `mass_zero` | theorem | Agent 4 |
| `mass_neg` | theorem | Agent 4 |
| `eval_le_flatNorm` | theorem | Agent 5 |
| `ofForm_sub` | theorem | Agent 3 |
| `SmoothForm.zero` | def | Agent 1 |

---

# 🔷 AGENT 1: SmoothForm Predicate (5 axioms)

**Goal:** Make `IsSmoothAlternating` constructive or prove these follow from structure.

| Axiom | File | Strategy |
|-------|------|----------|
| `isSmoothAlternating_zero` | Basic.lean | Define: `0` satisfies alternating |
| `isSmoothAlternating_add` | Basic.lean | Closure under addition |
| `isSmoothAlternating_neg` | Basic.lean | Closure under negation |
| `isSmoothAlternating_smul` | Basic.lean | Closure under scalar mult |
| `isSmoothAlternating_sub` | Basic.lean | `sub = add ∘ neg` |

**Approach:** If `IsSmoothAlternating` is defined as a predicate on functions, these should follow from the algebraic structure of `AlternatingMap`.

---

# 🔷 AGENT 2: Exterior Derivative Linearity (3 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `smoothExtDeriv_add` | Basic.lean | d is linear map |
| `smoothExtDeriv_smul` | Basic.lean | d is ℂ-linear |
| `smoothExtDeriv_smul_real` | Basic.lean | d is ℝ-linear |

**Approach:** If `smoothExtDeriv` wraps Mathlib's `exteriorDerivative`, these follow from linearity. Check how `smoothExtDeriv` is defined.

---

# 🔷 AGENT 3: Quotient + Topology (2 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `ofForm_smul_real` | Basic.lean | Quotient.sound |
| `SmoothForm.instTopologicalSpace` | Basic.lean | Use Mathlib topology |

**Approach for `ofForm_smul_real`:**
```lean
theorem ofForm_smul_real (r : ℝ) (ω) (hω) :
    ⟦r • ω, _⟧ = r • ⟦ω, hω⟧ := by
  apply Quotient.sound
  unfold Cohomologous IsExact
  -- r • ω - r • ω' = r • (ω - ω') is exact if ω - ω' is exact
```

---

# 🔷 AGENT 4: Flat Norm Properties (3 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `eval_le_mass` | FlatNorm.lean | Use mass definition |
| `flatNorm_boundary_le` | FlatNorm.lean | Flat norm estimate |
| `flatNorm_eq_zero_iff` | FlatNorm.lean | Infimum = 0 ↔ T = 0 |

**Approach:** These depend on how `flatNorm` is defined. Check if it's an infimum over decompositions.

---

# 🔷 AGENT 5: Comass Properties (3 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `pointwiseComass_nonneg` | Norms.lean | Supremum of norms ≥ 0 |
| `pointwiseComass_zero` | Norms.lean | Supremum over empty = 0 |
| `conePositive_comass_bound` | Microstructure.lean | Document as interface |

**Approach:** If `comass` is a supremum of absolute values, these follow from norm properties.

---

# 🔷 AGENT 6: Kähler Power Properties (4 axioms) — **HIGH PRIORITY**

| Axiom | File | Hodge Weight |
|-------|------|--------------|
| `omega_pow_IsFormClosed` | TypeDecomp.lean | **HIGH** |
| `omega_pow_is_rational` | TypeDecomp.lean | **HIGH** |
| `omegaPow_in_interior` | Cone.lean | **HIGH** |
| `shift_makes_conePositive_rat` | Cone.lean | **HIGH** |

**Approach:**
- `omega_pow_IsFormClosed`: d(ω^p) = 0 by induction using d(ω) = 0 and product rule
- `omega_pow_is_rational`: Uses integral cohomology of Kähler manifolds
- These are core Hodge theory — may require deep Mathlib

---

# 🔷 AGENT 7: Calibration (4 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `wirtinger_comass_bound` | Calibration.lean | Classical pillar |
| `simpleCalibratedForm` | Grassmannian.lean | Volume form |
| `omega_pow_represents_multiple` | Main.lean | Classical pillar |
| `RawSheetSum.toIntegralCurrent_toFun_eq_zero` | Microstructure.lean | Technical |

**Note:** `wirtinger_comass_bound` is a classical result from calibration theory.

---

# 🔷 AGENT 8: Classical Pillars (6 axioms) — **DOCUMENT ONLY**

These are acceptable as axioms. **Document** why they're classical pillars:

| Axiom | Reference | Status |
|-------|-----------|--------|
| `serre_gaga` | Serre 1956 | ✓ Documented |
| `flat_limit_existence` | FF 1960 | ✓ Documented |
| `mass_lsc` | Federer 1969 | ✓ Documented |
| `calibration_defect_from_gluing` | FF 1960 | ✓ Documented |
| `harvey_lawson_fundamental_class` | HL 1983 | Needs documentation |
| `lefschetz_lift_signed_cycle` | Hard Lefschetz | Needs documentation |

**Task:** Add docstrings explaining why these are classical pillars that require extensive Mathlib infrastructure to prove.

---

## Summary

| Agent | Count | Type | Priority |
|-------|-------|------|----------|
| **1** | 5 | Interface (SmoothForm) | 🟡 |
| **2** | 3 | Interface (Derivative) | 🟡 |
| **3** | 2 | Quotient + Topology | 🟡 |
| **4** | 3 | Flat Norm | 🟢 Medium |
| **5** | 3 | Comass | 🟢 Medium |
| **6** | 4 | **Kähler Powers** | 🟢 **HIGH** |
| **7** | 4 | Calibration | 🟢 Medium |
| **8** | 6 | Classical Pillars | 🔴 Document |

**Total:** 30 axioms

---

## Target End State

After this round:
- **~6 classical pillars** remain as documented axioms
- **~0 interface axioms** (prove or document as opaque-type structure)
- **~0 Hodge-weight axioms** (must be proved)

---

## Verification Command

```bash
lake env lean DependencyCheck.lean 2>&1 | tail -n +2 | tr ',[]' '\n' | sed 's/^ *//' | grep -v "^$" | grep -v "propext\|Classical.choice\|Quot.sound" | grep -v "depends on axioms" | sort | uniq | wc -l
```

**Current:** 30 → **Target:** 6 (classical pillars only)
