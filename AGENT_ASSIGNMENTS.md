# Agent Assignments: 16 Hodge-Weight Axioms → 8 Agents

**Mission:** Prove the 16 Hodge-Weight axioms that carry mathematical substance.

**Status:** Round 16  
**Progress:** 44 → 30 axioms (6 classical pillars + 8 interface + **16 Hodge-Weight**)

---

## ⚠️ CRITICAL RULES

1. **TEST LOCALLY**: `lake build Hodge` before commit
2. **NO FORWARD REFERENCES**: Define theorems BEFORE using them
3. **IF IT DOESN'T COMPILE → LEAVE AS AXIOM**
4. **ONE FILE AT A TIME**
5. **NO `sorry`, `admit`, or stub definitions**

---

## Classification Summary

| Category | Count | Action |
|----------|-------|--------|
| 🔴 Classical Pillars | 6 | Keep as axioms (deep theorems) |
| 🟡 Interface Axioms | 8 | Structural — separate effort |
| 🟢 **Hodge-Weight** | **16** | **MUST PROVE — assigned below** |

---

## The 16 Hodge-Weight Axioms

These carry mathematical substance and must be proven:

```
conePositive_comass_bound          pointwiseComass_nonneg
eval_le_mass                       pointwiseComass_zero
flatNorm_boundary_le               RawSheetSum.toIntegralCurrent_toFun_eq_zero
flatNorm_eq_zero_iff               shift_makes_conePositive_rat
ofForm_smul_real                   simpleCalibratedForm
omegaPow_in_interior               smoothExtDeriv_smul_real
omega_pow_IsFormClosed             wirtinger_comass_bound
omega_pow_is_rational              omega_pow_represents_multiple
```

---

# 🔷 AGENT 1: Kähler Closure (2 axioms) — **CRITICAL**

**File:** `Hodge/Kahler/TypeDecomposition.lean`

| Axiom | Strategy |
|-------|----------|
| `omega_pow_IsFormClosed` | d(ω^p) = 0 by induction: d(ω^{p+1}) = d(ω ∧ ω^p) = dω ∧ ω^p + ω ∧ d(ω^p) = 0 |
| `omega_pow_is_rational` | [ω^p] ∈ H(X,ℚ) — Kähler class is integral, powers are rational |

**Key insight:** Use `kahler_form_closed` (dω = 0) and product rule for exterior derivative.

---

# 🔷 AGENT 2: Cone Positivity (2 axioms) — **CRITICAL**

**File:** `Hodge/Kahler/Cone.lean`

| Axiom | Strategy |
|-------|----------|
| `omegaPow_in_interior` | ω^p lies in interior of strongly positive cone K_p |
| `shift_makes_conePositive_rat` | γ + c·ω^p is cone-positive for some rational c > 0 |

**Key insight:** ω^p is strictly positive definite on complex p-planes (Wirtinger).

---

# 🔷 AGENT 3: Algebraicity (2 axioms)

**Files:** `Hodge/Kahler/Main.lean`, `Hodge/Basic.lean`

| Axiom | Strategy |
|-------|----------|
| `omega_pow_represents_multiple` | c·[ω^p] is algebraic for some c > 0 |
| `ofForm_smul_real` | [r·ω] = r·[ω] — use `Quotient.sound` and `ofForm_proof_irrel` |

---

# 🔷 AGENT 4: Flat Norm (2 axioms)

**File:** `Hodge/Analytic/FlatNorm.lean`

| Axiom | Strategy |
|-------|----------|
| `flatNorm_boundary_le` | ‖∂T‖_flat ≤ ‖T‖_flat — boundary doesn't increase flat norm |
| `flatNorm_eq_zero_iff` | ‖T‖_flat = 0 ↔ T = 0 — flat norm separates points |

**Key insight:** Use `flatNorm` definition as infimum over decompositions.

---

# 🔷 AGENT 5: Mass & Evaluation (2 axioms)

**Files:** `Hodge/Analytic/FlatNorm.lean`, `Hodge/Basic.lean`

| Axiom | Strategy |
|-------|----------|
| `eval_le_mass` | \|T(ψ)\| ≤ mass(T) × comass(ψ) — duality |
| `smoothExtDeriv_smul_real` | d(r·ω) = r·dω — real scalar linearity |

---

# 🔷 AGENT 6: Comass (2 axioms)

**File:** `Hodge/Analytic/Norms.lean`

| Axiom | Strategy |
|-------|----------|
| `pointwiseComass_nonneg` | comass ≥ 0 — supremum of absolute values |
| `pointwiseComass_zero` | comass(0) = 0 — supremum over zero is zero |

**Key insight:** `comass` is defined as `sSup { |ω(ξ)| : ‖ξ‖ ≤ 1 }`.

---

# 🔷 AGENT 7: Calibration (2 axioms)

**Files:** `Hodge/Analytic/Calibration.lean`, `Hodge/Analytic/Grassmannian.lean`

| Axiom | Strategy |
|-------|----------|
| `wirtinger_comass_bound` | Wirtinger inequality: ω^p has comass 1 on complex p-planes |
| `simpleCalibratedForm` | Simple calibrated form exists (volume form on subspace) |

---

# 🔷 AGENT 8: Microstructure (2 axioms)

**File:** `Hodge/Kahler/Microstructure.lean`

| Axiom | Strategy |
|-------|----------|
| `conePositive_comass_bound` | Cone-positive forms have bounded comass ≤ 2 |
| `RawSheetSum.toIntegralCurrent_toFun_eq_zero` | Technical: sheet sum gives zero current |

---

## Summary

| Agent | Axioms | Focus | File |
|-------|--------|-------|------|
| **1** | 2 | Kähler closure | TypeDecomposition.lean |
| **2** | 2 | Cone positivity | Cone.lean |
| **3** | 2 | Algebraicity | Main.lean, Basic.lean |
| **4** | 2 | Flat norm | FlatNorm.lean |
| **5** | 2 | Mass & evaluation | FlatNorm.lean, Basic.lean |
| **6** | 2 | Comass | Norms.lean |
| **7** | 2 | Calibration | Calibration.lean, Grassmannian.lean |
| **8** | 2 | Microstructure | Microstructure.lean |

**Total:** 16 Hodge-Weight axioms

---

## NOT ASSIGNED (Acceptable as Axioms)

### 🔴 Classical Pillars (6)
- `serre_gaga` — Serre GAGA 1956
- `flat_limit_existence` — Federer-Fleming 1960
- `mass_lsc` — Federer 1969
- `calibration_defect_from_gluing` — FF 1960
- `harvey_lawson_fundamental_class` — Harvey-Lawson 1983
- `lefschetz_lift_signed_cycle` — Hard Lefschetz

### 🟡 Interface Axioms (8)
- `isSmoothAlternating_zero/add/neg/smul/sub` (5)
- `smoothExtDeriv_add`, `smoothExtDeriv_smul` (2)
- `SmoothForm.instTopologicalSpace` (1)

---

## Verification

```bash
# Build must pass
lake build Hodge

# Count axioms in proof chain (should decrease from 30)
lake env lean DependencyCheck.lean 2>&1 | tail -n +2 | tr ',[]' '\n' | \
  sed 's/^ *//' | grep -v "^$" | \
  grep -v "propext\|Classical.choice\|Quot.sound" | \
  grep -v "depends on axioms" | sort | uniq | wc -l
```

**Current:** 30 → **Target:** 14 (6 classical + 8 interface)

---

## Quick Start

```bash
git pull origin main
# Edit your assigned file(s)
lake build Hodge
git add -A && git commit -m "Agent N: Prove [axiom_name]" && git push
```
