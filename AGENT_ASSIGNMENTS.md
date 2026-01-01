# Agent Assignments: Prove 44 Axioms

**Mission:** Prove all 44 axioms in `hodge_conjecture'` proof chain.

**Success:** `#print axioms hodge_conjecture'` shows only `propext`, `Classical.choice`, `Quot.sound` (+ optionally `serre_gaga`).

---

## 🚫 RULES

1. **NO `sorry`, `admit`, `trivial`, `native_decide`**
2. **NO stub definitions** (`def mass := 0` is cheating)
3. **Build passes before claiming done:** `lake build Hodge`
4. **Verify axiom removed:** `lake env lean DependencyCheck.lean`

---

## Current Status

| Metric | Value |
|--------|-------|
| Build | ✅ Passes |
| Axioms in proof chain | **44** |
| Target | **0** (or 1 if keeping `serre_gaga`) |

---

# 🔷 AGENT 1: Form Structure + Quotient Operations (14 axioms)

## Target: Prove 14 axioms

### P5: Form/Cohomology Structure (10 axioms)

| # | Axiom | File:Line | Status |
|---|-------|-----------|--------|
| 25 | `SmoothForm.zero` | Basic.lean:71 | ❌ TODO |
| 26 | `SmoothForm.instAddCommGroup` | Basic.lean:80 | ❌ TODO |
| 27 | `SmoothForm.instModuleComplex` | Basic.lean:84 | ❌ TODO |
| 28 | `SmoothForm.instTopologicalSpace` | Basic.lean:93 | ❌ TODO |
| 29 | `smoothExtDeriv_add` | Basic.lean:113 | ❌ TODO |
| 30 | `smoothExtDeriv_smul` | Basic.lean:118 | ❌ TODO |
| 31 | `smoothExtDeriv_smul_real` | Basic.lean:123 | ❌ TODO |
| 32 | `instAddCommGroupDeRhamCohomologyClass` | Basic.lean:310 | ❌ TODO |
| 33 | `instModuleDeRhamCohomologyClass` | Basic.lean:324 | ❌ TODO |
| 34 | `smulRat_DeRhamCohomologyClass` | Basic.lean:332 | ❌ TODO |

### P6: Quotient Operations (4 axioms)

| # | Axiom | File:Line | Status |
|---|-------|-----------|--------|
| 35 | `ofForm_add` | Basic.lean:361 | ❌ TODO |
| 36 | `ofForm_sub` | Basic.lean:367 | ❌ TODO |
| 37 | `ofForm_smul_real` | Basic.lean:370 | ❌ TODO |
| 38 | `smul_rat_eq_smul_real` | Basic.lean:342 | ❌ TODO |

## Strategy

**For #25-28 (SmoothForm instances):**
- Option A: Replace `opaque SmoothForm` with concrete Mathlib `DifferentialForm`
- Option B: Define instances using the opaque + axioms pattern (keeps axioms but makes them instances)

**For #29-31 (smoothExtDeriv linearity):**
- These require `smoothExtDeriv` to be defined (not opaque) OR add definitional axiom
- Check if there's a `smoothExtDeriv_def` that connects to Mathlib's `exteriorDerivative`

**For #32-34 (DeRhamCohomologyClass module):**
- Use `Quotient.lift₂` to define addition on the quotient
- Prove well-definedness: if ω ≈ ω' and η ≈ η', then ω+η ≈ ω'+η'

**For #35-38 (ofForm operations):**
```lean
theorem ofForm_add {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    DeRhamCohomologyClass.ofForm (ω + η) (isFormClosed_add hω hη) =
    DeRhamCohomologyClass.ofForm ω hω + DeRhamCohomologyClass.ofForm η hη := by
  -- Use the quotient structure
  unfold DeRhamCohomologyClass.ofForm
  -- Apply Quotient.sound to show equivalence
  rfl  -- or appropriate quotient lemma
```

## Deliverables

- [ ] #35-38 proven (quotient operations) — **START HERE**
- [ ] #32-34 proven (module instances)
- [ ] #29-31 proven or documented why opaque blocks
- [ ] #25-28 addressed (instances or documented)

---

# 🔷 AGENT 2: Flat Norm / Mass (9 axioms)

## Target: Prove 9 axioms

### P3: Flat Norm / Mass

| # | Axiom | File:Line | Status |
|---|-------|-----------|--------|
| 8 | `flatNorm_nonneg` | FlatNorm.lean:32 | ❌ TODO |
| 9 | `flatNorm_zero` | FlatNorm.lean:35 | ❌ TODO |
| 10 | `eval_le_flatNorm` | FlatNorm.lean:45 | ❌ TODO |
| 11 | `flatNorm_le_mass` | FlatNorm.lean:50 | ❌ TODO |
| 12 | `flatNorm_neg` | FlatNorm.lean:56 | ❌ TODO |
| 13 | `flatNorm_eq_zero_iff` | FlatNorm.lean:59 | ❌ TODO |
| 14 | `flatNorm_boundary_le` | FlatNorm.lean:66 | ❌ TODO |
| 15 | `flat_limit_existence` | Microstructure.lean:192 | ❌ TODO |
| 16 | `mass_lsc` | Calibration.lean:116 | ❌ TODO |

## Strategy

**Check if `flatNorm` is opaque or defined:**
```bash
grep -n "opaque flatNorm\|def flatNorm" Hodge/Analytic/FlatNorm.lean
```

**If flatNorm is defined as infimum:**
```lean
-- flatNorm T = ⨅ {(S, R) | T = S + ∂R}, mass(S) + mass(R)

theorem flatNorm_nonneg : flatNorm T ≥ 0 := by
  -- Infimum of nonnegative quantities is nonnegative
  apply Real.iInf_nonneg
  intro ⟨S, R, _⟩
  exact add_nonneg (mass_nonneg S) (mass_nonneg R)

theorem flatNorm_zero : flatNorm (0 : Current n X k) = 0 := by
  -- Take S = 0, R = 0: then 0 = 0 + ∂0, and mass(0) + mass(0) = 0
  apply le_antisymm
  · exact ciInf_le_of_le ⟨0, 0, by simp⟩ (by simp [mass_zero])
  · exact flatNorm_nonneg

theorem flatNorm_le_mass : flatNorm T ≤ mass T := by
  -- Take S = T, R = 0: then T = T + ∂0
  exact ciInf_le_of_le ⟨T, 0, by simp⟩ (by simp [mass_zero])
```

**For #15-16 (classical results):**
- `flat_limit_existence`: Federer-Fleming compactness — may need to remain axiom
- `mass_lsc`: Lower semicontinuity — classical GMT, may need to remain axiom

## Deliverables

- [ ] #8-9 proven (nonneg, zero)
- [ ] #11-12 proven (le_mass, neg)
- [ ] #10, #13-14 proven or documented
- [ ] #15-16 documented as classical if needed

---

# 🔷 AGENT 3: Kähler / Calibration + Other (15 axioms)

## Target: Prove 15 axioms

### P4: Kähler / Calibration (8 axioms)

| # | Axiom | File:Line | Status |
|---|-------|-----------|--------|
| 17 | `wirtinger_comass_bound` | Calibration.lean:46 | ❌ TODO |
| 18 | `calibration_inequality` | Calibration.lean:65 | ❌ TODO |
| 19 | `simpleCalibratedForm` | Grassmannian.lean:106 | ❌ TODO |
| 20 | `omegaPow_in_interior` | Cone.lean:79 | ❌ TODO |
| 21 | `omega_pow_IsFormClosed` | TypeDecomp.lean:125 | ❌ TODO |
| 22 | `omega_pow_is_rational` | TypeDecomp.lean:128 | ❌ TODO |
| 23 | `omega_pow_represents_multiple` | Main.lean:173 | ❌ TODO |
| 24 | `shift_makes_conePositive_rat` | Cone.lean:173 | ❌ TODO |

### P7: Other (7 axioms)

| # | Axiom | File:Line | Status |
|---|-------|-----------|--------|
| 39 | `pointwiseComass_nonneg` | Norms.lean:41 | ❌ TODO |
| 40 | `polyhedral_zero` | IntegralCurrents.lean:42 | ❌ TODO |
| 41 | `serre_gaga` | GAGA.lean:149 | ⚠️ CLASSICAL |
| 42 | `isPPForm_zero` | Basic.lean:477 | ❌ TODO |
| 43 | `isRationalClass_zero` | Basic.lean:405 | ❌ TODO |
| 44 | `isRationalClass_add` | Basic.lean:413 | ❌ TODO |
| 45 | `isRationalClass_smul_rat` | Basic.lean:422 | ❌ TODO |

## Strategy

**For #21 (omega_pow_IsFormClosed):**
```lean
-- d(ω^p) = 0 follows from dω = 0 and d(α ∧ β) = dα ∧ β + (-1)^k α ∧ dβ
theorem omega_pow_IsFormClosed (p : ℕ) : IsFormClosed (kahlerPow p) := by
  induction p with
  | zero => exact isFormClosed_one  -- ω^0 = 1, d(1) = 0
  | succ p ih =>
    -- ω^{p+1} = ω ∧ ω^p
    -- d(ω^{p+1}) = dω ∧ ω^p + ω ∧ d(ω^p) = 0 ∧ ω^p + ω ∧ 0 = 0
    apply isFormClosed_wedge
    exact omega_closed  -- dω = 0
    exact ih
```

**For #39 (pointwiseComass_nonneg):**
```lean
theorem pointwiseComass_nonneg : pointwiseComass ω x ≥ 0 := by
  -- Supremum of absolute values is nonnegative
  apply Real.sSup_nonneg
  intro y hy
  obtain ⟨v, _, rfl⟩ := hy
  exact abs_nonneg _
```

**For #42-45 (rational class properties):**
```lean
theorem isRationalClass_zero : isRationalClass (0 : DeRhamCohomologyClass n X k) := by
  -- [0] = 0 · [anything rational], so it's rational
  use 0, someRationalClass
  simp

theorem isRationalClass_add (h1 : isRationalClass c1) (h2 : isRationalClass c2) :
    isRationalClass (c1 + c2) := by
  -- Rational classes form a ℚ-vector space
  obtain ⟨q1, base1, rfl⟩ := h1
  obtain ⟨q2, base2, rfl⟩ := h2
  -- Use common denominator...
```

**For #41 (serre_gaga):**
- This is Serre's GAGA theorem (1956)
- **Acceptable as the ONE classical pillar**

## Deliverables

- [ ] #39, #42-45 proven (basic properties)
- [ ] #21 proven (omega closed)
- [ ] #40 proven (polyhedral zero)
- [ ] #17-20, #22-24 addressed
- [ ] #41 documented as classical pillar

---

# 🔷 AGENT 4: Strategy-Critical (2 axioms)

## Target: Prove or properly axiomatize 2 axioms

### P1: Strategy-Critical

| # | Axiom | File:Line | Status |
|---|-------|-----------|--------|
| 1 | `harvey_lawson_fundamental_class` | Main.lean:112 | ❌ TODO |
| 2 | `lefschetz_lift_signed_cycle` | Main.lean:195 | ❌ TODO |

## Strategy

**These are the hardest axioms.** Options:

### Option A: Build Real Infrastructure

**For #1 (harvey_lawson_fundamental_class):**
1. Fix `harvey_lawson_theorem` to return actual varieties (not empty)
2. Define `represents` properly (not `fun _ => True`)
3. Prove the cohomology class equality

**For #2 (lefschetz_lift_signed_cycle):**
1. Use `hard_lefschetz_inverse_form` to get the inverse map
2. Show that if η is represented by Z_η, then L^{-1}(η) is represented by some Z
3. The key is showing algebraicity is preserved under Lefschetz

### Option B: Derive from Existing Structure

Check if these follow from other axioms we already have:
- `harvey_lawson_theorem` already exists as an axiom
- `hard_lefschetz_inverse_form` already exists
- Can we compose these to get what we need?

### Option C: Document as Classical Pillars

If neither A nor B works:
- Document these as requiring deep GMT/Hodge theory infrastructure
- They are legitimate deep theorems (Harvey-Lawson 1982, Voisin 2002)

## Investigation Steps

1. Read Main.lean:100-220 to understand the exact requirements
2. Check what `harvey_lawson_theorem` currently provides
3. Check what `hard_lefschetz_inverse_form` provides
4. Determine if composition gives us what we need

## Deliverables

- [ ] Investigation complete
- [ ] Strategy chosen (A, B, or C)
- [ ] Implementation or documentation complete

---

# 🔷 AGENT 5: Microstructure Construction (5 axioms)

## Target: Prove 5 axioms

### P2: Microstructure (Paper Constructions)

| # | Axiom | File:Line | Status |
|---|-------|-----------|--------|
| 3 | `cubulation_exists` | Microstructure.lean:147 | ❌ TODO |
| 4 | `calibration_defect_from_gluing` | Microstructure.lean:168 | ❌ TODO |
| 5 | `microstructureSequence_defect_bound_axiom` | Microstructure.lean:219 | ❌ TODO |
| 6 | `microstructureSequence_mass_bound_axiom` | Microstructure.lean:241 | ❌ TODO |
| 7 | `RawSheetSum.toIntegralCurrent_isCycle` | Microstructure.lean:116 | ❌ TODO |

## Strategy

**These encode YOUR paper's construction. They MUST be proven.**

**For #3 (cubulation_exists):**
```lean
-- A cubulation of scale h exists for any h > 0
-- This is a combinatorial/geometric construction
axiom cubulation_exists (h : ℝ) (hh : h > 0) : Cubulation n X h

-- To prove: Define Cubulation concretely using Mathlib's grid/lattice structures
-- Then construct one explicitly
```

**For #7 (RawSheetSum.toIntegralCurrent_isCycle):**
```lean
-- The boundary of a sheet sum is zero
-- This follows from: sheets are closed surfaces, boundaries cancel in pairs

theorem RawSheetSum.toIntegralCurrent_isCycle : 
    boundary (RawSheetSum.toIntegralCurrent rss) = 0 := by
  -- Each sheet is a closed oriented surface
  -- When we sum with coefficients, boundaries cancel
  unfold RawSheetSum.toIntegralCurrent
  simp only [boundary_sum]
  -- Show each sheet has zero boundary (closed manifold)
  -- Or show boundaries cancel in pairs
```

**For #4-6 (defect and mass bounds):**
- These follow from the explicit construction in the paper
- Reference: Hodge-v6-w-Jon-Update-MERGED.tex, Section 11

## Key Insight

The microstructure axioms are not "deep classical theorems" — they are **constructive** results from the paper. They should be provable once the definitions are made concrete.

**Check current state:**
```bash
grep -n "structure Cubulation\|def Cubulation\|opaque Cubulation" Hodge/Kahler/Microstructure.lean
```

## Deliverables

- [ ] Audit current Cubulation/RawSheetSum definitions
- [ ] #7 proven (cycle property)
- [ ] #3 proven (cubulation exists)
- [ ] #4-6 proven (bounds from construction)

---

# Summary

| Agent | Priority | Axiom Count | Key Focus |
|-------|----------|-------------|-----------|
| **1** | P5, P6 | 14 | Quotient operations, module structure |
| **2** | P3 | 9 | Flat norm properties |
| **3** | P4, P7 | 15 | Kähler geometry, rational classes |
| **4** | P1 | 2 | **Strategy-critical** (hardest) |
| **5** | P2 | 5 | **Microstructure** (paper constructions) |

---

# Verification

After each session, run:
```bash
lake env lean DependencyCheck.lean 2>&1 | grep -v "propext\|Classical.choice\|Quot.sound" | wc -l
```

Target: This number should decrease toward 0 (or 1 if keeping `serre_gaga`).
