# Agent Assignments: 30 Proof-Chain Axioms → 8 Agents

**Status:** Ready for Round 16  
**Progress:** 44 → 30 axioms in proof chain  
**Total axioms in codebase:** ~113 (only 30 block `hodge_conjecture'`)

---

## ⚠️ CRITICAL RULES — READ BEFORE CODING

1. **TEST LOCALLY FIRST**: Run `lake build Hodge` before any commit
2. **NO FORWARD REFERENCES**: Define theorems BEFORE using them
3. **IF IT DOESN'T COMPILE → LEAVE AS AXIOM**: Don't break the build
4. **ONE FILE AT A TIME**: Don't edit multiple files in one session
5. **NO `sorry`, `admit`, or stub definitions**

---

## Quick Start for Each Agent

```bash
# 1. Pull latest
git pull origin main

# 2. Make your changes to ONE file

# 3. Test build
lake build Hodge

# 4. If build passes, commit and push
git add -A && git commit -m "Agent N: [description]" && git push
```

---

## The 30 Axioms in Proof Chain

Verified via `lake env lean DependencyCheck.lean`:

```
calibration_defect_from_gluing     omegaPow_in_interior
conePositive_comass_bound          omega_pow_IsFormClosed
eval_le_mass                       omega_pow_is_rational
flatNorm_boundary_le               omega_pow_represents_multiple
flatNorm_eq_zero_iff               pointwiseComass_nonneg
flat_limit_existence               pointwiseComass_zero
harvey_lawson_fundamental_class    RawSheetSum.toIntegralCurrent_toFun_eq_zero
isSmoothAlternating_add            serre_gaga
isSmoothAlternating_neg            shift_makes_conePositive_rat
isSmoothAlternating_smul           simpleCalibratedForm
isSmoothAlternating_sub            smoothExtDeriv_add
isSmoothAlternating_zero           smoothExtDeriv_smul
lefschetz_lift_signed_cycle        smoothExtDeriv_smul_real
mass_lsc                           SmoothForm.instTopologicalSpace
ofForm_smul_real                   wirtinger_comass_bound
```

---

# 🔷 AGENT 1: `isSmoothAlternating_*` (5 axioms)

**File:** `Hodge/Basic.lean` (lines 84-92)

| Axiom | Line | Strategy |
|-------|------|----------|
| `isSmoothAlternating_zero` | 84 | Zero function is alternating |
| `isSmoothAlternating_add` | 85 | Sum of alternating is alternating |
| `isSmoothAlternating_neg` | 87 | Negation preserves alternating |
| `isSmoothAlternating_smul` | 89 | Scalar mult preserves alternating |
| `isSmoothAlternating_sub` | 91 | sub = add ∘ neg |

**Approach:** These follow from `AlternatingMap` being a submodule. Check if `IsSmoothAlternating` can be defined constructively.

---

# 🔷 AGENT 2: `smoothExtDeriv_*` (3 axioms)

**File:** `Hodge/Basic.lean` (lines 157-169)

| Axiom | Line | Strategy |
|-------|------|----------|
| `smoothExtDeriv_add` | 157 | d(ω + η) = dω + dη |
| `smoothExtDeriv_smul` | 162 | d(c • ω) = c • dω |
| `smoothExtDeriv_smul_real` | 167 | d(r • ω) = r • dω |

**Approach:** If `smoothExtDeriv` wraps a linear map, these follow from linearity.

---

# 🔷 AGENT 3: Quotient + Topology (2 axioms)

**Files:** `Hodge/Basic.lean`

| Axiom | Strategy |
|-------|----------|
| `ofForm_smul_real` | Use `Quotient.sound` and `ofForm_proof_irrel` |
| `SmoothForm.instTopologicalSpace` | Interface axiom — document or use Mathlib |

---

# 🔷 AGENT 4: Flat Norm (3 axioms)

**File:** `Hodge/Analytic/FlatNorm.lean`

| Axiom | Strategy |
|-------|----------|
| `eval_le_mass` | T(ψ) ≤ mass(T) × comass(ψ) — use mass definition |
| `flatNorm_boundary_le` | ‖∂T‖ ≤ ‖T‖ — flat norm estimate |
| `flatNorm_eq_zero_iff` | ‖T‖ = 0 ↔ T = 0 — separation |

---

# 🔷 AGENT 5: Comass (3 axioms)

**Files:** `Hodge/Analytic/Norms.lean`, `Hodge/Kahler/Microstructure.lean`

| Axiom | Strategy |
|-------|----------|
| `pointwiseComass_nonneg` | Supremum of norms ≥ 0 |
| `pointwiseComass_zero` | comass(0) = 0 |
| `conePositive_comass_bound` | Document as interface axiom |

---

# 🔷 AGENT 6: Kähler Powers (4 axioms) — **HIGH PRIORITY**

**Files:** `Hodge/Kahler/TypeDecomposition.lean`, `Hodge/Kahler/Cone.lean`

| Axiom | Hodge Weight |
|-------|--------------|
| `omega_pow_IsFormClosed` | **CRITICAL** — d(ω^p) = 0 |
| `omega_pow_is_rational` | **CRITICAL** — [ω^p] ∈ H(X,ℚ) |
| `omegaPow_in_interior` | **CRITICAL** — ω^p in cone interior |
| `shift_makes_conePositive_rat` | **HIGH** — rational shift |

---

# 🔷 AGENT 7: Calibration (4 axioms)

**Files:** `Hodge/Analytic/Calibration.lean`, `Hodge/Kahler/Microstructure.lean`

| Axiom | Strategy |
|-------|----------|
| `wirtinger_comass_bound` | Classical Wirtinger inequality |
| `simpleCalibratedForm` | Volume form calibration |
| `omega_pow_represents_multiple` | May be classical pillar |
| `RawSheetSum.toIntegralCurrent_toFun_eq_zero` | Technical — document |

---

# 🔷 AGENT 8: Classical Pillars (6 axioms) — **DOCUMENT ONLY**

These are acceptable as final axioms. Add comprehensive docstrings:

| Axiom | Reference | File |
|-------|-----------|------|
| `serre_gaga` | Serre 1956 | GAGA.lean |
| `flat_limit_existence` | FF 1960 | Microstructure.lean |
| `mass_lsc` | Federer 1969 | Calibration.lean |
| `calibration_defect_from_gluing` | FF 1960 | Microstructure.lean |
| `harvey_lawson_fundamental_class` | HL 1983 | Main.lean |
| `lefschetz_lift_signed_cycle` | Hard Lefschetz | Main.lean |

---

## Summary Table

| Agent | Axioms | Focus | Priority |
|-------|--------|-------|----------|
| 1 | 5 | `isSmoothAlternating_*` | 🟡 |
| 2 | 3 | `smoothExtDeriv_*` | 🟡 |
| 3 | 2 | Quotient + Topology | 🟡 |
| 4 | 3 | Flat Norm | 🟢 |
| 5 | 3 | Comass | 🟢 |
| **6** | **4** | **Kähler Powers** | **🔴 HIGH** |
| 7 | 4 | Calibration | 🟢 |
| 8 | 6 | Classical Pillars | 📝 Document |

---

## Verification

After making changes, verify:

```bash
# Build must pass
lake build Hodge

# Check axiom count in proof chain
lake env lean DependencyCheck.lean 2>&1 | grep -v "propext\|Classical.choice\|Quot.sound" | grep -v "depends on" | wc -l
```

**Current:** 30 → **Target:** 6 (classical pillars only)
