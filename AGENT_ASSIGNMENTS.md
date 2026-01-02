# Agent Assignments: Round 17 Update

**Progress:** 30 → 22 axioms (8 proved this round!)

---

## ✅ PROVED THIS ROUND (8 axioms!)

| Axiom | Agent |
|-------|-------|
| `omega_pow_IsFormClosed` | 1 |
| `smoothExtDeriv_smul_real` | 5 |
| `ofForm_smul_real` | 3 |
| `RawSheetSum.toIntegralCurrent_toFun_eq_zero` | 8 |
| `shift_makes_conePositive_rat` | 2 |
| `flatNorm_boundary_le` | 3 |
| `flatNorm_eq_zero_iff` | 3 |
| `eval_le_mass` | 4 |

---

## ⚠️ RULES

1. `lake build Hodge` before commit
2. Define theorems BEFORE using them
3. IF IT DOESN'T COMPILE → LEAVE AS AXIOM

---

# Remaining: 8 Hodge-Weight + 7 Interface = 15 axioms

---

## 🔷 AGENT 1: Kähler Rationality (2)

| Axiom | File |
|-------|------|
| `omega_pow_is_rational` | TypeDecomposition.lean |
| `omega_pow_represents_multiple` | Main.lean |

---

## 🔷 AGENT 2: Cone + Comass (3)

| Axiom | File |
|-------|------|
| `omegaPow_in_interior` | Cone.lean |
| `pointwiseComass_nonneg` | Norms.lean |
| `pointwiseComass_zero` | Norms.lean |

---

## 🔷 AGENT 3: Interface - Alternating (3)

| Axiom | File |
|-------|------|
| `isSmoothAlternating_zero` | Basic.lean |
| `isSmoothAlternating_add` | Basic.lean |
| `isSmoothAlternating_neg` | Basic.lean |

---

## 🔷 AGENT 4: Interface - Deriv + Alternating (4)

| Axiom | File |
|-------|------|
| `isSmoothAlternating_smul` | Basic.lean |
| `isSmoothAlternating_sub` | Basic.lean |
| `smoothExtDeriv_add` | Basic.lean |
| `smoothExtDeriv_smul` | Basic.lean |

---

## 🔷 AGENT 5: Available

All original axioms proved! Can assist other agents.

---

## 🔷 AGENT 6: Calibration (2)

| Axiom | File |
|-------|------|
| `wirtinger_comass_bound` | Calibration.lean |
| `simpleCalibratedForm` | Grassmannian.lean |

---

## 🔷 AGENT 7: Microstructure (1)

| Axiom | File |
|-------|------|
| `conePositive_comass_bound` | Microstructure.lean |

---

## 🔷 AGENT 8: Available

All original axioms proved! Can assist other agents.

---

## Summary

| Agent | Count | Status |
|-------|-------|--------|
| 1 | 2 | Hodge-Weight |
| 2 | 3 | Hodge-Weight |
| 3 | 3 | Interface |
| 4 | 4 | Interface |
| 5 | 0 | ✅ Available |
| 6 | 2 | Hodge-Weight |
| 7 | 1 | Hodge-Weight |
| 8 | 0 | ✅ Available |

**Total remaining:** 15 axioms  
**Target:** 6 classical pillars only

---

## Classical Pillars (Keep as Axioms)

- `serre_gaga`
- `flat_limit_existence`
- `mass_lsc`
- `calibration_defect_from_gluing`
- `harvey_lawson_fundamental_class`
- `lefschetz_lift_signed_cycle`
