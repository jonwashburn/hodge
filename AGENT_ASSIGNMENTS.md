# Agent Assignments: 12 Remaining Hodge-Weight Axioms → 8 Agents

**Status:** Round 17  
**Progress:** 16 Hodge-Weight → **12 remaining** (4 proved this round!)

---

## ✅ PROVED THIS ROUND

| Axiom | Now | Agent |
|-------|-----|-------|
| `omega_pow_IsFormClosed` | **THEOREM** | Agent 1 |
| `smoothExtDeriv_smul_real` | **THEOREM** | Agent 5 |
| `ofForm_smul_real` | **THEOREM** | Agent 3 |
| `RawSheetSum.toIntegralCurrent_toFun_eq_zero` | **THEOREM** | Agent 8 |

**Great progress! 4 Hodge-Weight axioms converted to theorems.**

---

## ⚠️ CRITICAL RULES

1. **TEST LOCALLY**: `lake build Hodge` before commit
2. **NO FORWARD REFERENCES**: Define theorems BEFORE using them
3. **IF IT DOESN'T COMPILE → LEAVE AS AXIOM**
4. **ONE FILE AT A TIME**

---

## The 12 Remaining Hodge-Weight Axioms

```
conePositive_comass_bound          pointwiseComass_zero
eval_le_mass                       shift_makes_conePositive_rat
flatNorm_boundary_le               simpleCalibratedForm
flatNorm_eq_zero_iff               wirtinger_comass_bound
omegaPow_in_interior               omega_pow_is_rational
pointwiseComass_nonneg             omega_pow_represents_multiple
```

---

# 🔷 AGENT 1: Kähler Rationality (2 axioms) — **CRITICAL**

**File:** `Hodge/Kahler/TypeDecomposition.lean`

| Axiom | Strategy |
|-------|----------|
| `omega_pow_is_rational` | [ω^p] ∈ H(X,ℚ) — Kähler class is integral |
| `omega_pow_represents_multiple` | c·[ω^p] is algebraic for some c > 0 |

---

# 🔷 AGENT 2: Cone Positivity (2 axioms) — **CRITICAL**

**File:** `Hodge/Kahler/Cone.lean`

| Axiom | Strategy |
|-------|----------|
| `omegaPow_in_interior` | ω^p lies in interior of strongly positive cone |
| `shift_makes_conePositive_rat` | γ + c·ω^p is cone-positive for some rational c > 0 |

---

# 🔷 AGENT 3: Flat Norm (2 axioms)

**File:** `Hodge/Analytic/FlatNorm.lean`

| Axiom | Strategy |
|-------|----------|
| `flatNorm_boundary_le` | ‖∂T‖_flat ≤ ‖T‖_flat |
| `flatNorm_eq_zero_iff` | ‖T‖_flat = 0 ↔ T = 0 |

---

# 🔷 AGENT 4: Mass & Evaluation (1 axiom)

**File:** `Hodge/Analytic/FlatNorm.lean`

| Axiom | Strategy |
|-------|----------|
| `eval_le_mass` | \|T(ψ)\| ≤ mass(T) × comass(ψ) |

**Note:** This agent has 1 axiom — can help other agents or work on interface axioms.

---

# 🔷 AGENT 5: Comass (2 axioms)

**File:** `Hodge/Analytic/Norms.lean`

| Axiom | Strategy |
|-------|----------|
| `pointwiseComass_nonneg` | comass ≥ 0 — supremum of absolute values |
| `pointwiseComass_zero` | comass(0) = 0 |

---

# 🔷 AGENT 6: Calibration (2 axioms)

**Files:** `Hodge/Analytic/Calibration.lean`, `Hodge/Analytic/Grassmannian.lean`

| Axiom | Strategy |
|-------|----------|
| `wirtinger_comass_bound` | Wirtinger inequality |
| `simpleCalibratedForm` | Simple calibrated form exists |

---

# 🔷 AGENT 7: Microstructure (1 axiom)

**File:** `Hodge/Kahler/Microstructure.lean`

| Axiom | Strategy |
|-------|----------|
| `conePositive_comass_bound` | Cone-positive forms have bounded comass ≤ 2 |

**Note:** This agent has 1 axiom — can help other agents or work on interface axioms.

---

# 🔷 AGENT 8: Interface Axioms (bonus)

Work on the 8 interface axioms if Hodge-Weight is blocked:

| Axiom | File |
|-------|------|
| `isSmoothAlternating_zero` | Basic.lean |
| `isSmoothAlternating_add` | Basic.lean |
| `isSmoothAlternating_neg` | Basic.lean |
| `isSmoothAlternating_smul` | Basic.lean |
| `isSmoothAlternating_sub` | Basic.lean |
| `smoothExtDeriv_add` | Basic.lean |
| `smoothExtDeriv_smul` | Basic.lean |
| `SmoothForm.instTopologicalSpace` | Basic.lean |

---

## Summary

| Agent | Remaining | Focus |
|-------|-----------|-------|
| **1** | 2 | Kähler rationality |
| **2** | 2 | Cone positivity |
| **3** | 2 | Flat norm |
| **4** | 1 | Mass & evaluation |
| **5** | 2 | Comass |
| **6** | 2 | Calibration |
| **7** | 1 | Microstructure |
| **8** | 0 (+8 interface) | Interface axioms |

**Total Hodge-Weight remaining:** 12

---

## Axiom Counts

| Category | Original | Remaining |
|----------|----------|-----------|
| Hodge-Weight | 16 | **12** |
| Interface | 8 | 8 |
| Classical Pillars | 6 | 6 |
| **Total in proof chain** | 30 | **26** |

---

## Target

**Current:** 26 axioms → **Target:** 14 (6 classical + 8 interface)

Need to prove: **12 more Hodge-Weight axioms**

---

## Quick Start

```bash
git pull origin main
# Edit your assigned file(s)
lake build Hodge
git add -A && git commit -m "Agent N: Prove [axiom_name]" && git push
```
