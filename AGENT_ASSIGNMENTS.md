# Agent Assignments: 25 Axioms → 8 Agents

**Build:** ❌ FAILS (Fixing Hodge.Basic)
**Progress:** 44 → 35 → 32 → 30 → 25 axioms  
**Verified:** 25 axioms in `hodge_conjecture'` proof chain via `DependencyCheck.lean`

---

## 🚫 CRITICAL RULES

1. **NO `sorry`, `admit`, `native_decide`**
2. **NO stub definitions** (e.g., `def mass := 0`)
3. **Build MUST pass:** `lake build Hodge`
4. **Test before commit:** Forward references will break build
5. **IF PROOF DOESN'T WORK CLEANLY → LEAVE AS AXIOM**

---

## Axiom Classification

### 🔴 CLASSICAL PILLARS — 8 axioms (Acceptable as Final Axioms)

These are deep theorems requiring extensive Mathlib infrastructure:

| Axiom | Reference | Complexity | Status |
|-------|-----------|------------|--------|
| `serre_gaga` | Serre GAGA 1956 | ~10,000 LOC | ✓ Documented |
| `flat_limit_existence` | Federer-Fleming 1960 | ~5,000 LOC | ✓ Documented |
| `mass_lsc` | Federer 1969 | ~3,000 LOC | ✓ Documented |
| `calibration_defect_from_gluing` | FF Gluing 1960 | ~5,000 LOC | ✓ Documented |
| `harvey_lawson_fundamental_class` | Harvey-Lawson 1983 | ~8,000 LOC | ✓ Documented |
| `lefschetz_lift_signed_cycle` | Hard Lefschetz | ~6,000 LOC | ✓ Documented |
| `omega_pow_is_rational` | Kähler/Hodge Theory | ~5,000 LOC | ✓ **PROVED** (theorem) |
| `omegaPow_in_interior` | Demailly 2012 | ~4,000 LOC | ✓ Documented |
| `omega_pow_represents_multiple` | Griffiths-Harris 1978 | ~7,000 LOC | ✓ Documented |

### 🟡 INTERFACE AXIOMS — 10 axioms (Structural)

Define algebraic structure on opaque types:

| Axiom | Type | Notes | Status |
|-------|------|-------|--------|
| `smoothExtDeriv_add` | Derivative | d(ω+η) = dω + dη | ✓ PROVED |
| `smoothExtDeriv_smul` | Derivative | d(c·ω) = c·dω | ✓ PROVED |
| `pointwiseComass_nonneg` | Comass | Sup norm is non-negative | Pending |
| `pointwiseComass_zero` | Comass | Sup norm of 0 is 0 | Pending |
| `pointwiseComass_smul` | Comass | Homogeneity | Pending |
| `pointwiseComass_continuous` | Comass | Continuity | Pending |
| `comass_eq_zero_iff` | Comass | Norm property | Pending |
| `Current.boundary_boundary` | Current | ∂² = 0 | Pending |
| `Current.is_bounded` | Current | Continuity | Pending |
| `ofForm_smul_real` | Quotient | [r·ω] = r·[ω] | Pending |

### 🟢 HODGE-WEIGHT AXIOMS — 6 axioms (Must Prove)

These carry mathematical substance for the proof:

| Priority | Axiom | Hodge Weight | Status |
|----------|-------|--------------|--------|
| **P1** | `omega_pow_IsFormClosed` | **CRITICAL** — d(ω^p) = 0 | Pending |
| **P2** | `shift_makes_conePositive_rat` | **HIGH** — rational shift | Pending |
| **P2** | `wirtinger_comass_bound` | **HIGH** — Wirtinger inequality | Pending |
| **P3** | `simpleCalibratedForm` | **MEDIUM** — volume form | Pending |
| **P3** | `conePositive_comass_bound` | **MEDIUM** — uniform bound | Pending |
| **P5** | `RawSheetSum.toIntegralCurrent_toFun_eq_zero` | **LOW** — technical | Pending |

---

# Agent Assignments

## 🔷 AGENT 1: Proved Axioms (Cleanup)
- `isSmoothAlternating_*` (5 axioms) -> **PROVED**
- `SmoothForm.instTopologicalSpace` -> **PROVED**
- `smoothExtDeriv_smul_real` -> **PROVED**
- `eval_le_mass` -> **PROVED**
- `flatNorm_boundary_le` -> **PROVED**
- `flatNorm_eq_zero_iff` -> **PROVED**

## 🔷 AGENT 2: Exterior Derivative (2 axioms) → **PROVED**
- `smoothExtDeriv_add` → **THEOREM** (via `map_add` on `smoothExtDerivLM`)
- `smoothExtDeriv_smul` → **THEOREM** (via `map_smul` on `smoothExtDerivLM`)

## 🔷 AGENT 5: Comass Interface (7 axioms)
- `pointwiseComass_nonneg`
- `pointwiseComass_zero`
- `pointwiseComass_smul`
- `pointwiseComass_continuous`
- `comass_eq_zero_iff`
- `conePositive_comass_bound`
- `wirtinger_comass_bound` (Reassigned)

## 🔷 AGENT 6: Kähler Powers (3 axioms)
- `omega_pow_IsFormClosed`
- `shift_makes_conePositive_rat`
- `simpleCalibratedForm` (Reassigned)

## 🔷 AGENT 7: Currents & Calibration (3 axioms)
- `Current.boundary_boundary`
- `Current.is_bounded`
- `RawSheetSum.toIntegralCurrent_toFun_eq_zero`

## 🔷 AGENT 8: Classical Pillars (8 axioms) — **DOCUMENT ONLY**
- Documented 8 deep theorems with STATUS markers.
- `omega_pow_is_rational` is now a **PROVED THEOREM** (not an axiom).

---

## Summary

| Agent | Axioms | Type | Priority |
|-------|--------|------|----------|
| 1 | 0 | Cleanup | ✓ |
| 2 | 0 | Interface | ✓ PROVED |
| 5 | 7 | Comass | 🟢 Medium |
| **6** | **3** | **Kähler** | 🟢 **HIGH** |
| 7 | 3 | Currents | 🟢 Medium |
| 8 | 8 | Classical | 🔴 Document ✓ |

---

## Verification

```bash
lake env lean DependencyCheck.lean 2>&1 | tail -n +2 | tr ',[]' '\n' | \
  sed 's/^ *//' | grep -v "^$" | \
  grep -v "propext\|Classical.choice\|Quot.sound" | \
  grep -v "depends on axioms" | sort | uniq | wc -l
```

**Current:** 24 → **Target:** 8 classical pillars
