# Agent Assignments: 32 Axioms → 8 Agents

**Mission:** Prove all 32 axioms in `hodge_conjecture'` proof chain.

**Progress:** 44 → 35 → 32 axioms

**Success:** `#print axioms hodge_conjecture'` shows only `propext`, `Classical.choice`, `Quot.sound` (+ ~5 classical pillars)

---

## 🚫 RULES

1. **NO `sorry`, `admit`, `trivial`, `native_decide`**
2. **NO stub definitions** 
3. **Build passes:** `lake build Hodge`
4. **Verify:** `lake env lean DependencyCheck.lean`

---

## Current Status

| Metric | Value |
|--------|-------|
| Build | ✅ Passes |
| Axioms in proof chain | **32** |
| Target | **~5** classical pillars |

---

## The 32 Axioms

```
calibration_defect_from_gluing     omega_pow_IsFormClosed
conePositive_comass_bound          omega_pow_is_rational
Current.mass_neg                   omega_pow_represents_multiple
Current.mass_nonneg                pointwiseComass_nonneg
Current.mass_zero                  RawSheetSum.toIntegralCurrent_toFun_eq_zero
eval_le_flatNorm                   serre_gaga
eval_le_mass                       shift_makes_conePositive_rat
flatNorm_boundary_le               simpleCalibratedForm
flatNorm_eq_zero_iff               smoothExtDeriv_add
flat_limit_existence               smoothExtDeriv_smul
harvey_lawson_fundamental_class    smoothExtDeriv_smul_real
lefschetz_lift_signed_cycle        SmoothForm.instAddCommGroup
mass_lsc                           SmoothForm.instModuleComplex
ofForm_smul_real                   SmoothForm.instTopologicalSpace
ofForm_sub                         SmoothForm.zero
omegaPow_in_interior               wirtinger_comass_bound
```

---

# 🔷 AGENT 1: SmoothForm Structure (4 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `SmoothForm.zero` | Basic.lean | Interface axiom |
| `SmoothForm.instAddCommGroup` | Basic.lean | Interface axiom |
| `SmoothForm.instModuleComplex` | Basic.lean | Interface axiom |
| `SmoothForm.instTopologicalSpace` | Basic.lean | Interface axiom |

**Strategy:** These are interface axioms for the opaque `SmoothForm` type. Options:
1. Replace `opaque SmoothForm` with Mathlib's `DifferentialForm`
2. Document as foundational interface (acceptable if truly opaque)

---

# 🔷 AGENT 2: Exterior Derivative Linearity (3 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `smoothExtDeriv_add` | Basic.lean | d(ω + η) = dω + dη |
| `smoothExtDeriv_smul` | Basic.lean | d(c·ω) = c·dω |
| `smoothExtDeriv_smul_real` | Basic.lean | d(r·ω) = r·dω |

**Strategy:** If `smoothExtDeriv` is connected to Mathlib's `exteriorDerivative`, these follow from linearity. Check for a definitional axiom.

---

# 🔷 AGENT 3: Quotient Operations (2 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `ofForm_sub` | Basic.lean | [ω - η] = [ω] - [η] |
| `ofForm_smul_real` | Basic.lean | [r·ω] = r·[ω] |

**Strategy:** Use `Quotient.sound`:
```lean
theorem ofForm_sub (ω η) (hω hη) :
    ofForm (ω - η) _ = ofForm ω hω - ofForm η hη := by
  apply Quotient.sound
  -- Show: Cohomologous ⟨ω - η, _⟩ ⟨..., _⟩
```

---

# 🔷 AGENT 4: Mass Properties (3 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `Current.mass_nonneg` | Currents.lean | mass ≥ 0 |
| `Current.mass_zero` | Currents.lean | mass(0) = 0 |
| `Current.mass_neg` | Currents.lean | mass(-T) = mass(T) |

**Strategy:** If `mass` is defined as supremum:
```lean
theorem Current.mass_nonneg : mass T ≥ 0 := by
  -- Supremum of nonneg quantities is nonneg
```

---

# 🔷 AGENT 5: Flat Norm Properties (4 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `eval_le_flatNorm` | FlatNorm.lean | T(ψ) ≤ flatNorm T · comass ψ |
| `eval_le_mass` | FlatNorm.lean | T(ψ) ≤ mass T · comass ψ |
| `flatNorm_boundary_le` | FlatNorm.lean | flatNorm(∂T) ≤ flatNorm T |
| `flatNorm_eq_zero_iff` | FlatNorm.lean | flatNorm T = 0 ↔ T = 0 |

**Strategy:** These are fundamental flat norm estimates. Check if `flatNorm` has a concrete definition.

---

# 🔷 AGENT 6: Kähler / Calibration (6 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `omega_pow_IsFormClosed` | TypeDecomp.lean | d(ω^p) = 0 |
| `omega_pow_is_rational` | TypeDecomp.lean | [ω^p] ∈ H(X,ℚ) |
| `omega_pow_represents_multiple` | Main.lean | c·[ω^p] algebraic |
| `omegaPow_in_interior` | Cone.lean | ω^p in interior |
| `pointwiseComass_nonneg` | Norms.lean | comass ≥ 0 |
| `conePositive_comass_bound` | Cone.lean | Comass bound |

**Priority:** Start with `omega_pow_IsFormClosed` (induction on p) and `pointwiseComass_nonneg` (sup of nonneg).

---

# 🔷 AGENT 7: Calibration + Cone (5 axioms)

| Axiom | File | Strategy |
|-------|------|----------|
| `wirtinger_comass_bound` | Calibration.lean | Wirtinger inequality |
| `simpleCalibratedForm` | Grassmannian.lean | Volume form |
| `shift_makes_conePositive_rat` | Cone.lean | γ + c·ω^p positive |
| `mass_lsc` | Calibration.lean | Lower semicontinuity |
| `flat_limit_existence` | Microstructure.lean | FF compactness |

**Note:** `mass_lsc` and `flat_limit_existence` are classical GMT results — may remain as axioms.

---

# 🔷 AGENT 8: Strategy-Critical + Microstructure (5 axioms)

| Axiom | File | Status |
|-------|------|--------|
| `harvey_lawson_fundamental_class` | Main.lean | ⚠️ CRITICAL |
| `lefschetz_lift_signed_cycle` | Main.lean | ⚠️ CRITICAL |
| `calibration_defect_from_gluing` | Microstructure.lean | Classical pillar |
| `RawSheetSum.toIntegralCurrent_toFun_eq_zero` | Microstructure.lean | Cast issue |
| `serre_gaga` | GAGA.lean | Classical pillar |

**Strategy for #1-2:**
1. Investigate `harvey_lawson_theorem` structure
2. Check if derivable from existing axioms
3. If not, document as classical pillars

---

# Summary

| Agent | Axioms | Focus |
|-------|--------|-------|
| **1** | 4 | SmoothForm interface |
| **2** | 3 | Exterior derivative linearity |
| **3** | 2 | Quotient operations |
| **4** | 3 | Mass properties |
| **5** | 4 | Flat norm properties |
| **6** | 6 | Kähler / omega powers |
| **7** | 5 | Calibration + cone |
| **8** | 5 | **Strategy-critical** + microstructure |

**Total:** 32 axioms

---

## Classical Pillars (Acceptable as Axioms)

These are deep theorems from the literature:
1. `serre_gaga` — Serre's GAGA (1956)
2. `flat_limit_existence` — Federer-Fleming compactness (1960)
3. `mass_lsc` — Lower semicontinuity of mass
4. `calibration_defect_from_gluing` — GMT gluing estimate
5. `harvey_lawson_fundamental_class` — HL fundamental class
6. `lefschetz_lift_signed_cycle` — Lefschetz on cycles

---

## Verification

```bash
lake env lean DependencyCheck.lean 2>&1 | tail -n +2 | tr ',[]' '\n' | sed 's/^ *//' | grep -v "^$" | grep -v "propext\|Classical.choice\|Quot.sound" | grep -v "depends on axioms" | sort | uniq | wc -l
```

**Current:** 32 → **Target:** ~6 classical pillars
