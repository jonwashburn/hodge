# Agent Assignments: Prove 35 Axioms

**Mission:** Prove all 35 axioms in `hodge_conjecture'` proof chain.

**Progress:** 44 → 35 axioms (-9 in last round!)

**Success:** `#print axioms hodge_conjecture'` shows only `propext`, `Classical.choice`, `Quot.sound` (+ optionally `serre_gaga`).

---

## 🚫 RULES

1. **NO `sorry`, `admit`, `trivial`, `native_decide`**
2. **NO stub definitions** (`def mass := 0` is cheating)
3. **Build passes before claiming done:** `lake build Hodge`
4. **Verify axiom removed:** `lake env lean DependencyCheck.lean`

---

## Current Status (After Round 13)

| Metric | Value |
|--------|-------|
| Build | ✅ Passes |
| Axioms in proof chain | **35** (was 44) |
| Target | **0** (or 1 if keeping `serre_gaga`) |

---

## The 35 Remaining Axioms

```
calibration_defect_from_gluing     harvey_lawson_fundamental_class
calibration_inequality             instAddCommGroupDeRhamCohomologyClass
conePositive_comass_bound          instModuleDeRhamCohomologyClass
eval_le_flatNorm                   lefschetz_lift_signed_cycle
flatNorm_boundary_le               mass_lsc
flatNorm_eq_zero_iff               ofForm_add
flatNorm_neg                       ofForm_smul_real
flat_limit_existence               ofForm_sub
gluing_mass_bound                  omegaPow_in_interior
omega_pow_IsFormClosed             shift_makes_conePositive_rat
omega_pow_is_rational              simpleCalibratedForm
omega_pow_represents_multiple      smoothExtDeriv_add
pointwiseComass_nonneg             smoothExtDeriv_smul
serre_gaga                         smoothExtDeriv_smul_real
wirtinger_comass_bound             Current.mass_nonneg
Current.mass_zero                  RawSheetSum.toIntegralCurrent_isCycle
SmoothForm.instAddCommGroup        SmoothForm.instModuleComplex
SmoothForm.instTopologicalSpace    SmoothForm.zero
```

---

# 🔷 AGENT 1: Form Structure + Quotient Operations (11 axioms)

## Your Axioms

| # | Axiom | File | Status |
|---|-------|------|--------|
| 1 | `SmoothForm.zero` | Basic.lean | ❌ TODO |
| 2 | `SmoothForm.instAddCommGroup` | Basic.lean | ❌ TODO |
| 3 | `SmoothForm.instModuleComplex` | Basic.lean | ❌ TODO |
| 4 | `SmoothForm.instTopologicalSpace` | Basic.lean | ❌ TODO |
| 5 | `smoothExtDeriv_add` | Basic.lean | ❌ TODO |
| 6 | `smoothExtDeriv_smul` | Basic.lean | ❌ TODO |
| 7 | `smoothExtDeriv_smul_real` | Basic.lean | ❌ TODO |
| 8 | `instAddCommGroupDeRhamCohomologyClass` | Basic.lean | ❌ TODO |
| 9 | `instModuleDeRhamCohomologyClass` | Basic.lean | ❌ TODO |
| 10 | `ofForm_add` | Basic.lean | ❌ TODO |
| 11 | `ofForm_sub` | Basic.lean | ❌ TODO |
| 12 | `ofForm_smul_real` | Basic.lean | ❌ TODO |

## Strategy

**Priority: #10-12 (ofForm operations)**
- Use `Quotient.sound` to show cohomologous forms give same class
- Pattern:
```lean
theorem ofForm_add (ω η : SmoothForm n X k) (hω hη) :
    ofForm (ω + η) _ = ofForm ω hω + ofForm η hη := by
  apply Quotient.sound
  show Cohomologous ⟨ω + η, _⟩ ⟨ω + η, _⟩  -- trivial
```

**#8-9 (instances):** Define using `Quotient.lift₂`

**#1-7 (SmoothForm):** These are interface axioms for the opaque type. Options:
- Replace `opaque SmoothForm` with Mathlib `DifferentialForm`
- Or document as foundational interface

---

# 🔷 AGENT 2: Flat Norm / Mass (7 axioms)

## Your Axioms

| # | Axiom | File | Status |
|---|-------|------|--------|
| 1 | `eval_le_flatNorm` | FlatNorm.lean | ❌ TODO |
| 2 | `flatNorm_boundary_le` | FlatNorm.lean | ❌ TODO |
| 3 | `flatNorm_eq_zero_iff` | FlatNorm.lean | ❌ TODO |
| 4 | `flatNorm_neg` | FlatNorm.lean | ❌ TODO |
| 5 | `flat_limit_existence` | Microstructure.lean | ❌ TODO |
| 6 | `mass_lsc` | Calibration.lean | ❌ TODO |
| 7 | `Current.mass_nonneg` | Currents.lean | ❌ TODO |
| 8 | `Current.mass_zero` | Currents.lean | ❌ TODO |

## Strategy

**Priority: #7-8 (mass properties)**
```lean
theorem Current.mass_nonneg (T : Current n X k) : mass T ≥ 0 := by
  -- mass is supremum of evaluations, which are bounded by comass
  -- All quantities are nonnegative

theorem Current.mass_zero : mass (0 : Current n X k) = 0 := by
  -- 0 current evaluates to 0 on all forms
```

**#3-4 (flatNorm properties):**
```lean
theorem flatNorm_neg (T) : flatNorm (-T) = flatNorm T := by
  -- Infimum is symmetric under negation

theorem flatNorm_eq_zero_iff (T) : flatNorm T = 0 ↔ T = 0 := by
  -- flatNorm = 0 means T can be written as ∂R with mass(R) → 0
```

**#5-6 (classical):** May need to remain as axioms (Federer-Fleming compactness, LSC)

---

# 🔷 AGENT 3: Kähler / Calibration (10 axioms)

## Your Axioms

| # | Axiom | File | Status |
|---|-------|------|--------|
| 1 | `wirtinger_comass_bound` | Calibration.lean | ❌ TODO |
| 2 | `calibration_inequality` | Calibration.lean | ❌ TODO |
| 3 | `simpleCalibratedForm` | Grassmannian.lean | ❌ TODO |
| 4 | `omegaPow_in_interior` | Cone.lean | ❌ TODO |
| 5 | `omega_pow_IsFormClosed` | TypeDecomp.lean | ❌ TODO |
| 6 | `omega_pow_is_rational` | TypeDecomp.lean | ❌ TODO |
| 7 | `omega_pow_represents_multiple` | Main.lean | ❌ TODO |
| 8 | `shift_makes_conePositive_rat` | Cone.lean | ❌ TODO |
| 9 | `pointwiseComass_nonneg` | Norms.lean | ❌ TODO |
| 10 | `conePositive_comass_bound` | Cone.lean | ❌ TODO |

## Strategy

**Priority: #5, #9 (simple properties)**
```lean
theorem omega_pow_IsFormClosed (p : ℕ) : IsFormClosed (kahlerPow p) := by
  -- d(ω^p) = 0 by induction: d(ω^0) = d(1) = 0, d(ω^{k+1}) = d(ω ∧ ω^k) = 0

theorem pointwiseComass_nonneg : pointwiseComass ω x ≥ 0 := by
  -- Supremum of absolute values is nonnegative
```

**#1-2 (calibration):** Classical results (Wirtinger, Harvey-Lawson)

**#10 (conePositive_comass_bound):** New axiom - check definition and prove from cone structure

---

# 🔷 AGENT 4: Strategy-Critical (2 axioms)

## Your Axioms

| # | Axiom | File | Status |
|---|-------|------|--------|
| 1 | `harvey_lawson_fundamental_class` | Main.lean:112 | ❌ TODO |
| 2 | `lefschetz_lift_signed_cycle` | Main.lean:195 | ❌ TODO |

## Strategy

**These are the hardest axioms.** 

### Investigation Tasks

1. **Read Main.lean:100-220** to understand exact requirements
2. **Check `harvey_lawson_theorem`** - what does it provide?
3. **Check `hard_lefschetz_inverse_form`** - can we use it?

### Options

**Option A:** Build real infrastructure
- Fix `harvey_lawson_theorem` to return actual varieties
- Prove cohomology equality from the representation

**Option B:** Derive from existing axioms
- Compose existing axioms to get what we need

**Option C:** Document as classical pillars
- These are deep theorems (Harvey-Lawson 1982, Voisin 2002)
- Acceptable if truly infeasible

---

# 🔷 AGENT 5: Microstructure + GAGA (6 axioms)

## Your Axioms

| # | Axiom | File | Status |
|---|-------|------|--------|
| 1 | `calibration_defect_from_gluing` | Microstructure.lean | ❌ TODO |
| 2 | `gluing_mass_bound` | Microstructure.lean | ❌ TODO |
| 3 | `RawSheetSum.toIntegralCurrent_isCycle` | Microstructure.lean | ❌ TODO |
| 4 | `flat_limit_existence` | Microstructure.lean | ❌ TODO |
| 5 | `serre_gaga` | GAGA.lean | ⚠️ CLASSICAL PILLAR |

## Strategy

**Priority: #3 (cycle property)**
```lean
theorem RawSheetSum.toIntegralCurrent_isCycle : 
    boundary (RawSheetSum.toIntegralCurrent rss) = 0 := by
  -- Sheet sum has zero boundary because:
  -- 1. Each sheet is a closed oriented surface
  -- 2. Boundaries cancel when summed with appropriate coefficients
```

**#1-2 (gluing bounds):**
- Follow paper construction (Section 11)
- Prove from explicit gluing formulas

**#4 (flat_limit_existence):**
- Federer-Fleming compactness
- May need to remain as axiom

**#5 (serre_gaga):**
- **CLASSICAL PILLAR** - Serre's GAGA theorem (1956)
- Acceptable to keep as the ONE allowed deep theorem

---

# Summary

| Agent | Axiom Count | Focus |
|-------|-------------|-------|
| **1** | 12 | Form structure, quotient operations |
| **2** | 8 | Flat norm, mass properties |
| **3** | 10 | Kähler/calibration |
| **4** | 2 | **Strategy-critical** (hardest) |
| **5** | 6 | Microstructure + GAGA |

**Total:** 35 axioms (+ 3 Lean system axioms)

---

# Verification

After each session:
```bash
lake env lean DependencyCheck.lean 2>&1 | grep -E "^ " | grep -v "propext\|Classical.choice\|Quot.sound" | wc -l
```

**Current:** 35  
**Target:** 0 (or 1 with `serre_gaga`)
