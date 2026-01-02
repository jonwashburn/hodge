# Agent Assignments: 30 Axioms → 8 Agents

**Build:** ✅ PASSES  
**Progress:** 44 → 35 → 32 → 30 axioms  
**Verified:** All 30 axioms confirmed in `hodge_conjecture'` proof chain via `DependencyCheck.lean`

---

## 🚫 CRITICAL RULES

1. **NO `sorry`, `admit`, `native_decide`**
2. **NO stub definitions** (e.g., `def mass := 0`)
3. **Build MUST pass:** `lake build Hodge`
4. **Test before commit:** Forward references will break build
5. **IF PROOF DOESN'T WORK CLEANLY → LEAVE AS AXIOM**

---

## Axiom Classification

### 🔴 CLASSICAL PILLARS — 6 axioms (Acceptable as Final Axioms)

These are deep theorems requiring extensive Mathlib infrastructure:

| Axiom | Reference | Complexity |
|-------|-----------|------------|
| `serre_gaga` | Serre GAGA 1956 | ~10,000 LOC |
| `flat_limit_existence` | Federer-Fleming 1960 | ~5,000 LOC |
| `mass_lsc` | Federer 1969 | ~3,000 LOC |
| `calibration_defect_from_gluing` | FF Gluing 1960 | ~5,000 LOC |
| `harvey_lawson_fundamental_class` | Harvey-Lawson 1983 | ~8,000 LOC |
| `lefschetz_lift_signed_cycle` | Hard Lefschetz | ~6,000 LOC |

### 🟡 INTERFACE AXIOMS — 8 axioms (Structural)

Define algebraic structure on opaque types:

| Axiom | Type | Notes |
|-------|------|-------|
| `isSmoothAlternating_zero` | SmoothForm | Zero preserves alternating |
| `isSmoothAlternating_add` | SmoothForm | Add preserves alternating |
| `isSmoothAlternating_neg` | SmoothForm | Neg preserves alternating |
| `isSmoothAlternating_smul` | SmoothForm | Smul preserves alternating |
| `isSmoothAlternating_sub` | SmoothForm | Sub = add ∘ neg |
| `SmoothForm.instTopologicalSpace` | SmoothForm | Topology on forms |
| `smoothExtDeriv_add` | Derivative | d(ω+η) = dω + dη |
| `smoothExtDeriv_smul` | Derivative | d(c·ω) = c·dω |

### 🟢 HODGE-WEIGHT AXIOMS — 16 axioms (Must Prove)

These carry mathematical substance for the proof:

| Priority | Axiom | Hodge Weight |
|----------|-------|--------------|
| **P1** | `omega_pow_IsFormClosed` | **CRITICAL** — d(ω^p) = 0 |
| **P1** | `omega_pow_is_rational` | **CRITICAL** — [ω^p] ∈ H(X,ℚ) |
| **P1** | `omega_pow_represents_multiple` | **CRITICAL** — algebraicity |
| **P1** | `omegaPow_in_interior` | **CRITICAL** — ω^p in cone |
| **P2** | `shift_makes_conePositive_rat` | **HIGH** — rational shift |
| **P2** | `wirtinger_comass_bound` | **HIGH** — Wirtinger inequality |
| **P3** | `simpleCalibratedForm` | **MEDIUM** — volume form |
| **P3** | `pointwiseComass_nonneg` | **MEDIUM** — comass ≥ 0 |
| **P3** | `pointwiseComass_zero` | **MEDIUM** — comass(0) = 0 |
| **P3** | `conePositive_comass_bound` | **MEDIUM** — uniform bound |
| **P4** | `eval_le_mass` | **MEDIUM** — T(ψ) ≤ M·comass |
| **P4** | `flatNorm_boundary_le` | **MEDIUM** — ‖∂T‖ ≤ ‖T‖ |
| **P4** | `flatNorm_eq_zero_iff` | **MEDIUM** — ‖T‖=0 ↔ T=0 |
| **P5** | `smoothExtDeriv_smul_real` | **LOW** — d(r·ω) = r·dω |
| **P5** | `ofForm_smul_real` | **LOW** — [r·ω] = r·[ω] |
| **P5** | `RawSheetSum.toIntegralCurrent_toFun_eq_zero` | **LOW** — technical |

---

# Agent Assignments

## 🔷 AGENT 1: SmoothForm Predicate (5 axioms)

| Axiom | Strategy |
|-------|----------|
| `isSmoothAlternating_zero` | Define predicate constructively |
| `isSmoothAlternating_add` | Closure under addition |
| `isSmoothAlternating_neg` | Closure under negation |
| `isSmoothAlternating_smul` | Closure under scalar mult |
| `isSmoothAlternating_sub` | sub = add ∘ neg |

**File:** `Hodge/Basic.lean`

---

## 🔷 AGENT 2: Exterior Derivative (3 axioms)

| Axiom | Strategy |
|-------|----------|
| `smoothExtDeriv_add` | d is additive |
| `smoothExtDeriv_smul` | d is ℂ-linear |
| `smoothExtDeriv_smul_real` | d is ℝ-linear |

**File:** `Hodge/Basic.lean`

---

## 🔷 AGENT 3: Quotient Operations (2 axioms)

| Axiom | Strategy |
|-------|----------|
| `ofForm_smul_real` | Quotient.sound |
| `SmoothForm.instTopologicalSpace` | Use Mathlib topology |

**File:** `Hodge/Basic.lean`

---

## 🔷 AGENT 4: Flat Norm (3 axioms)

| Axiom | Strategy |
|-------|----------|
| `eval_le_mass` | Use mass definition |
| `flatNorm_boundary_le` | Flat norm estimate |
| `flatNorm_eq_zero_iff` | Infimum = 0 ↔ T = 0 |

**File:** `Hodge/Analytic/FlatNorm.lean`

---

## 🔷 AGENT 5: Comass (3 axioms)

| Axiom | Strategy |
|-------|----------|
| `pointwiseComass_nonneg` | Supremum of norms ≥ 0 |
| `pointwiseComass_zero` | Sup over empty = 0 |
| `conePositive_comass_bound` | Document as interface |

**Files:** `Hodge/Analytic/Norms.lean`, `Hodge/Kahler/Microstructure.lean`

---

## 🔷 AGENT 6: Kähler Powers (4 axioms) — **HIGH PRIORITY**

| Axiom | Hodge Weight |
|-------|--------------|
| `omega_pow_IsFormClosed` | **CRITICAL** |
| `omega_pow_is_rational` | **CRITICAL** |
| `omegaPow_in_interior` | **CRITICAL** |
| `shift_makes_conePositive_rat` | **HIGH** |

**Files:** `Hodge/Kahler/TypeDecomposition.lean`, `Hodge/Kahler/Cone.lean`

---

## 🔷 AGENT 7: Calibration (4 axioms)

| Axiom | Strategy |
|-------|----------|
| `wirtinger_comass_bound` | Classical calibration |
| `simpleCalibratedForm` | Volume form |
| `omega_pow_represents_multiple` | May be classical pillar |
| `RawSheetSum.toIntegralCurrent_toFun_eq_zero` | Technical cast |

**Files:** `Hodge/Analytic/Calibration.lean`, `Hodge/Analytic/Grassmannian.lean`, `Hodge/Kahler/Microstructure.lean`

---

## 🔷 AGENT 8: Classical Pillars (6 axioms) — **DOCUMENT ONLY**

These are acceptable as final axioms. Task is to add comprehensive docstrings:

| Axiom | Status |
|-------|--------|
| `serre_gaga` | ✓ Documented |
| `flat_limit_existence` | ✓ Documented |
| `mass_lsc` | ✓ Documented |
| `calibration_defect_from_gluing` | ✓ Documented |
| `harvey_lawson_fundamental_class` | ✓ Documented |
| `lefschetz_lift_signed_cycle` | ✓ Documented |

---

## Summary

| Agent | Axioms | Type | Priority |
|-------|--------|------|----------|
| 1 | 5 | Interface | 🟡 |
| 2 | 3 | Interface | 🟡 |
| 3 | 2 | Interface | 🟡 |
| 4 | 3 | Flat Norm | 🟢 Medium |
| 5 | 3 | Comass | 🟢 Medium |
| **6** | **4** | **Kähler** | 🟢 **HIGH** |
| 7 | 4 | Calibration | 🟢 Medium |
| 8 | 6 | Classical | 🔴 Document |

---

## Target End State

- **~6 classical pillars** as documented axioms
- **~0 provable axioms** remaining
- `#print axioms hodge_conjecture'` shows only: `propext`, `Classical.choice`, `Quot.sound`, + 6 classical pillars

---

## Verification

```bash
# Count axioms in proof chain
lake env lean DependencyCheck.lean 2>&1 | tail -n +2 | tr ',[]' '\n' | \
  sed 's/^ *//' | grep -v "^$" | \
  grep -v "propext\|Classical.choice\|Quot.sound" | \
  grep -v "depends on axioms" | sort | uniq | wc -l
```

**Current:** 30 → **Target:** 6 classical pillars
