# Hodge Conjecture Formalization: Completion Plan

## Goal
Prove all 44 axioms in the `hodge_conjecture'` proof chain, leaving only Lean system axioms (propext, Classical.choice, Quot.sound).

---

## Current Status

| Metric | Value |
|--------|-------|
| **Build** | ✅ Passes |
| **Axioms in proof chain** | 44 |
| **Target** | 0 custom axioms |

---

## The 44 Axioms: Prioritized Checklist

### 🔴 P1: Strategy-Critical (2 axioms)

These encode the core mathematical strategy. **Highest priority.**

| # | Axiom | File:Line | Status | Owner | Notes |
|---|-------|-----------|--------|-------|-------|
| 1 | `harvey_lawson_fundamental_class` | Main.lean:112 | ❌ TODO | | Bridges current → cohomology class |
| 2 | `lefschetz_lift_signed_cycle` | Main.lean:195 | ❌ TODO | | Hard Lefschetz lift preserves algebraicity |

**Strategy:** These require either (a) building the Harvey-Lawson infrastructure properly, or (b) proving from existing axioms.

---

### 🟠 P2: Microstructure Construction (5 axioms)

These encode YOUR paper's construction. **Must be proven from the mathematical definitions.**

| # | Axiom | File:Line | Status | Owner | Notes |
|---|-------|-----------|--------|-------|-------|
| 3 | `cubulation_exists` | Microstructure.lean:147 | ❌ TODO | | Existence of h-cubulation |
| 4 | `calibration_defect_from_gluing` | Microstructure.lean:168 | ❌ TODO | | Defect bound from gluing |
| 5 | `microstructureSequence_defect_bound_axiom` | Microstructure.lean:219 | ❌ TODO | | Sequence defect → 0 |
| 6 | `microstructureSequence_mass_bound_axiom` | Microstructure.lean:241 | ❌ TODO | | Uniform mass bound |
| 7 | `RawSheetSum.toIntegralCurrent_isCycle` | Microstructure.lean:116 | ❌ TODO | | ∂(sheet sum) = 0 |

**Strategy:** These follow from the paper's constructions. Need to formalize the actual definitions.

---

### 🟡 P3: Flat Norm / Mass (9 axioms)

| # | Axiom | File:Line | Status | Owner | Notes |
|---|-------|-----------|--------|-------|-------|
| 8 | `flatNorm_nonneg` | FlatNorm.lean:32 | ❌ TODO | | Infimum of nonneg quantities |
| 9 | `flatNorm_zero` | FlatNorm.lean:35 | ❌ TODO | | 0 = inf{0 + 0} |
| 10 | `eval_le_flatNorm` | FlatNorm.lean:45 | ❌ TODO | | Duality estimate |
| 11 | `flatNorm_le_mass` | FlatNorm.lean:50 | ❌ TODO | | Take S = 0 in infimum |
| 12 | `flatNorm_neg` | FlatNorm.lean:56 | ❌ TODO | | Symmetry of norm |
| 13 | `flatNorm_eq_zero_iff` | FlatNorm.lean:59 | ❌ TODO | | Norm = 0 ↔ T = 0 |
| 14 | `flatNorm_boundary_le` | FlatNorm.lean:66 | ❌ TODO | | ‖∂T‖_F ≤ ‖T‖_F |
| 15 | `flat_limit_existence` | Microstructure.lean:192 | ❌ TODO | | Federer-Fleming compactness |
| 16 | `mass_lsc` | Calibration.lean:116 | ❌ TODO | | Lower semicontinuity |

**Strategy:** Properties 8-14 should follow from the flat norm definition. 15-16 are classical results.

---

### 🟡 P4: Kähler / Calibration (8 axioms)

| # | Axiom | File:Line | Status | Owner | Notes |
|---|-------|-----------|--------|-------|-------|
| 17 | `wirtinger_comass_bound` | Calibration.lean:46 | ❌ TODO | | Wirtinger inequality |
| 18 | `calibration_inequality` | Calibration.lean:65 | ❌ TODO | | T(ψ) ≤ mass(T) |
| 19 | `simpleCalibratedForm` | Grassmannian.lean:106 | ❌ TODO | | Volume form on calibrated planes |
| 20 | `omegaPow_in_interior` | Cone.lean:79 | ❌ TODO | | ω^p in interior of cone |
| 21 | `omega_pow_IsFormClosed` | TypeDecomp.lean:125 | ❌ TODO | | d(ω^p) = 0 |
| 22 | `omega_pow_is_rational` | TypeDecomp.lean:128 | ❌ TODO | | [ω^p] ∈ H²ᵖ(X,ℚ) |
| 23 | `omega_pow_represents_multiple` | Main.lean:173 | ❌ TODO | | c·[ω^p] is algebraic |
| 24 | `shift_makes_conePositive_rat` | Cone.lean:173 | ❌ TODO | | γ + c·ω^p is cone-positive |

**Strategy:** 17-18 are classical calibration results. 21 follows from dω = 0. Others need Kähler geometry.

---

### 🟢 P5: Form/Cohomology Structure (10 axioms)

| # | Axiom | File:Line | Status | Owner | Notes |
|---|-------|-----------|--------|-------|-------|
| 25 | `SmoothForm.zero` | Basic.lean:71 | ❌ TODO | | Zero form exists |
| 26 | `SmoothForm.instAddCommGroup` | Basic.lean:80 | ❌ TODO | | AddCommGroup instance |
| 27 | `SmoothForm.instModuleComplex` | Basic.lean:84 | ❌ TODO | | ℂ-module instance |
| 28 | `SmoothForm.instTopologicalSpace` | Basic.lean:93 | ❌ TODO | | Topology instance |
| 29 | `smoothExtDeriv_add` | Basic.lean:113 | ❌ TODO | | d(ω + η) = dω + dη |
| 30 | `smoothExtDeriv_smul` | Basic.lean:118 | ❌ TODO | | d(c·ω) = c·dω |
| 31 | `smoothExtDeriv_smul_real` | Basic.lean:123 | ❌ TODO | | d(r·ω) = r·dω |
| 32 | `instAddCommGroupDeRhamCohomologyClass` | Basic.lean:310 | ❌ TODO | | Quotient group |
| 33 | `instModuleDeRhamCohomologyClass` | Basic.lean:324 | ❌ TODO | | Quotient module |
| 34 | `smulRat_DeRhamCohomologyClass` | Basic.lean:332 | ❌ TODO | | ℚ-scaling |

**Strategy:** 25-28 are opaque type interfaces (need transparent definitions). 29-31 need d linear. 32-34 use Quotient.lift.

---

### 🟢 P6: Quotient Operations (4 axioms)

| # | Axiom | File:Line | Status | Owner | Notes |
|---|-------|-----------|--------|-------|-------|
| 35 | `ofForm_add` | Basic.lean:361 | ❌ TODO | | [ω + η] = [ω] + [η] |
| 36 | `ofForm_sub` | Basic.lean:367 | ❌ TODO | | [ω - η] = [ω] - [η] |
| 37 | `ofForm_smul_real` | Basic.lean:370 | ❌ TODO | | [r·ω] = r·[ω] |
| 38 | `smul_rat_eq_smul_real` | Basic.lean:342 | ❌ TODO | | q·[ω] = (q:ℝ)·[ω] |

**Strategy:** All provable using `Quotient.lift₂` and the cohomology equivalence relation.

---

### 🟢 P7: Other (7 axioms)

| # | Axiom | File:Line | Status | Owner | Notes |
|---|-------|-----------|--------|-------|-------|
| 39 | `pointwiseComass_nonneg` | Norms.lean:41 | ❌ TODO | | Norm ≥ 0 |
| 40 | `polyhedral_zero` | IntegralCurrents.lean:42 | ❌ TODO | | 0 ∈ polyhedral chains |
| 41 | `serre_gaga` | GAGA.lean:149 | ❌ TODO | | **CLASSICAL PILLAR** |
| 42 | `isPPForm_zero` | Basic.lean:477 | ❌ TODO | | 0 is a (p,p)-form |
| 43 | `isRationalClass_zero` | Basic.lean:405 | ❌ TODO | | [0] is rational |
| 44 | `isRationalClass_add` | Basic.lean:413 | ❌ TODO | | Closure under + |
| 45 | `isRationalClass_smul_rat` | Basic.lean:422 | ❌ TODO | | Closure under ℚ |

**Note:** `serre_gaga` (#41) is a deep theorem (Serre, 1956) — acceptable as the ONE classical pillar if needed.

---

## Agent Assignments

| Agent | Priority | Axioms | Target |
|-------|----------|--------|--------|
| **Agent 1** | P5, P6 | #29-38 (Form/Cohomology + Quotient) | 10 axioms |
| **Agent 2** | P3 | #8-16 (Flat Norm / Mass) | 9 axioms |
| **Agent 3** | P4, P7 | #17-24, #39-45 (Kähler + Other) | 15 axioms |
| **Agent 4** | P1 | #1-2 (Strategy-Critical) | 2 axioms |
| **Agent 5** | P2 | #3-7 (Microstructure) | 5 axioms |

---

## Proof Strategies by Category

### P1: Strategy-Critical

**`harvey_lawson_fundamental_class`:**
- Currently `harvey_lawson_theorem` returns empty varieties (stub)
- Need to: Either build actual variety construction OR prove the cohomology equality directly from existing axioms

**`lefschetz_lift_signed_cycle`:**
- Requires Hard Lefschetz inverse to preserve algebraicity
- Check if `hard_lefschetz_inverse_form` provides enough structure

### P2: Microstructure

These follow the paper's construction:
1. Define `Cubulation` concretely (not opaque)
2. Prove `cubulation_exists` using combinatorics
3. Build sheet sums with explicit boundary computation
4. Prove defect/mass bounds from the construction

### P6: Quotient Operations

Use this pattern:
```lean
theorem ofForm_add ... := by
  apply Quotient.sound
  -- Show: IsExact ((ω + η) - (ω' + η')) where ω ≈ ω', η ≈ η'
  -- This follows from IsExact being closed under addition
```

---

## Success Criteria

- [ ] `lake build Hodge` passes
- [ ] `#print axioms hodge_conjecture'` shows only:
  - `propext`
  - `Classical.choice`
  - `Quot.sound`
  - (optionally) `serre_gaga` as the one classical pillar

---

## Progress Tracking

| Date | Axioms Remaining | Notes |
|------|------------------|-------|
| 2026-01-01 | 44 | Initial count |
| 2026-01-01 | 35 | After Round 13 (-9 axioms) |
| | | |

---

## References

- Hodge-v6-w-Jon-Update-MERGED.tex (the paper)
- Harvey-Lawson, Acta Math. 148 (1982)
- Federer-Fleming, Ann. Math. 72 (1960)
- Serre, Ann. Inst. Fourier 6 (1956)

