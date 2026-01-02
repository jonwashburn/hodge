# Hodge Conjecture Formalization: Completion Plan

## Goal
Prove all axioms in the `hodge_conjecture'` proof chain, leaving only Lean system axioms (propext, Classical.choice, Quot.sound).

---

## Current Status

| Metric | Value |
|--------|-------|
| **Build** | ✅ Passes |
| **Axioms in proof chain** | **35** |
| **Target** | 0 custom axioms (or 1 with `serre_gaga`) |

---

## The 35 Axioms: Prioritized Checklist

### 🔴 P1: Strategy-Critical (2 axioms)

| # | Axiom | File | Status | Owner |
|---|-------|------|--------|-------|
| 1 | `harvey_lawson_fundamental_class` | Main.lean:112 | ❌ TODO | Agent 4 |
| 2 | `lefschetz_lift_signed_cycle` | Main.lean:195 | ❌ TODO | Agent 4 |

---

### 🟠 P2: Microstructure Construction (4 axioms)

| # | Axiom | File | Status | Owner |
|---|-------|------|--------|-------|
| 3 | `calibration_defect_from_gluing` | Microstructure.lean | ❌ TODO | Agent 5 |
| 4 | `gluing_mass_bound` | Microstructure.lean | ❌ TODO | Agent 5 |
| 5 | `RawSheetSum.toIntegralCurrent_isCycle` | Microstructure.lean | ❌ TODO | Agent 5 |
| 6 | `flat_limit_existence` | Microstructure.lean | ❌ TODO | Agent 5 |

---

### 🟡 P3: Flat Norm / Mass (6 axioms)

| # | Axiom | File | Status | Owner |
|---|-------|------|--------|-------|
| 7 | `eval_le_flatNorm` | FlatNorm.lean | ❌ TODO | Agent 2 |
| 8 | `flatNorm_boundary_le` | FlatNorm.lean | ❌ TODO | Agent 2 |
| 9 | `flatNorm_eq_zero_iff` | FlatNorm.lean | ❌ TODO | Agent 2 |
| 10 | `flatNorm_neg` | FlatNorm.lean | ❌ TODO | Agent 2 |
| 11 | `mass_lsc` | Calibration.lean | ❌ TODO | Agent 2 |
| 12 | `Current.mass_nonneg` | Currents.lean | ❌ TODO | Agent 2 |
| 13 | `Current.mass_zero` | Currents.lean | ❌ TODO | Agent 2 |

---

### 🟡 P4: Kähler / Calibration (10 axioms)

| # | Axiom | File | Status | Owner |
|---|-------|------|--------|-------|
| 14 | `wirtinger_comass_bound` | Calibration.lean | ❌ TODO | Agent 3 |
| 15 | `calibration_inequality` | Calibration.lean | ❌ TODO | Agent 3 |
| 16 | `simpleCalibratedForm` | Grassmannian.lean | ❌ TODO | Agent 3 |
| 17 | `omegaPow_in_interior` | Cone.lean | ❌ TODO | Agent 3 |
| 18 | `omega_pow_IsFormClosed` | TypeDecomp.lean | ❌ TODO | Agent 3 |
| 19 | `omega_pow_is_rational` | TypeDecomp.lean | ❌ TODO | Agent 3 |
| 20 | `omega_pow_represents_multiple` | Main.lean | ❌ TODO | Agent 3 |
| 21 | `shift_makes_conePositive_rat` | Cone.lean | ❌ TODO | Agent 3 |
| 22 | `conePositive_comass_bound` | Cone.lean | ❌ TODO | Agent 3 |
| 23 | `pointwiseComass_nonneg` | Norms.lean | ❌ TODO | Agent 3 |

---

### 🟢 P5: Form/Cohomology Structure (8 axioms)

| # | Axiom | File | Status | Owner |
|---|-------|------|--------|-------|
| 24 | `SmoothForm.zero` | Basic.lean | ❌ TODO | Agent 1 |
| 25 | `SmoothForm.instAddCommGroup` | Basic.lean | ❌ TODO | Agent 1 |
| 26 | `SmoothForm.instModuleComplex` | Basic.lean | ❌ TODO | Agent 1 |
| 27 | `SmoothForm.instTopologicalSpace` | Basic.lean | ❌ TODO | Agent 1 |
| 28 | `smoothExtDeriv_add` | Basic.lean | ❌ TODO | Agent 1 |
| 29 | `smoothExtDeriv_smul` | Basic.lean | ❌ TODO | Agent 1 |
| 30 | `smoothExtDeriv_smul_real` | Basic.lean | ❌ TODO | Agent 1 |
| 31 | `instAddCommGroupDeRhamCohomologyClass` | Basic.lean | ❌ TODO | Agent 1 |
| 32 | `instModuleDeRhamCohomologyClass` | Basic.lean | ❌ TODO | Agent 1 |

---

### 🟢 P6: Quotient Operations (3 axioms)

| # | Axiom | File | Status | Owner |
|---|-------|------|--------|-------|
| 33 | `ofForm_add` | Basic.lean | ❌ TODO | Agent 1 |
| 34 | `ofForm_sub` | Basic.lean | ❌ TODO | Agent 1 |
| 35 | `ofForm_smul_real` | Basic.lean | ❌ TODO | Agent 1 |

---

### 🟢 P7: Classical Pillar (1 axiom)

| # | Axiom | File | Status | Owner |
|---|-------|------|--------|-------|
| 36 | `serre_gaga` | GAGA.lean | ⚠️ CLASSICAL | Agent 5 |

**Note:** `serre_gaga` is Serre's GAGA theorem (1956) — acceptable as the ONE allowed deep theorem.

---

## Agent Assignments Summary

| Agent | Priority | Axiom Count | Focus |
|-------|----------|-------------|-------|
| **Agent 1** | P5, P6 | 12 | Form structure + quotient operations |
| **Agent 2** | P3 | 7 | Flat norm + mass properties |
| **Agent 3** | P4 | 10 | Kähler / calibration |
| **Agent 4** | P1 | 2 | **Strategy-critical** (hardest) |
| **Agent 5** | P2, P7 | 5 | Microstructure + GAGA |

---

## Proof Strategies

### P1: Strategy-Critical (Agent 4)

**`harvey_lawson_fundamental_class`:**
- Currently `harvey_lawson_theorem` returns empty varieties (stub)
- Options: Build actual variety construction OR derive from existing axioms

**`lefschetz_lift_signed_cycle`:**
- Use `hard_lefschetz_inverse_form` to construct the lift
- Show algebraicity is preserved

### P2: Microstructure (Agent 5)

1. Prove `RawSheetSum.toIntegralCurrent_isCycle` — boundary of sheet sum is zero
2. Prove `calibration_defect_from_gluing` — defect bound from explicit construction
3. Prove `gluing_mass_bound` — mass bound from gluing

### P3: Flat Norm (Agent 2)

```lean
theorem Current.mass_nonneg : mass T ≥ 0 := by
  -- mass is defined as supremum, all quantities nonneg

theorem flatNorm_neg : flatNorm (-T) = flatNorm T := by
  -- Symmetry of the infimum definition
```

### P5-P6: Form Structure (Agent 1)

```lean
theorem ofForm_add (ω η) (hω hη) :
    ofForm (ω + η) _ = ofForm ω hω + ofForm η hη := by
  apply Quotient.sound
  -- Show cohomologous: (ω + η) - (ω + η) is exact (trivially)
```

---

## Success Criteria

- [ ] `lake build Hodge` passes
- [ ] `#print axioms hodge_conjecture'` shows only:
  - `propext`
  - `Classical.choice`
  - `Quot.sound`
  - (optionally) `serre_gaga`

---

## Progress Tracking

| Date | Axioms Remaining | Notes |
|------|------------------|-------|
| 2026-01-01 | 44 | Initial count |
| 2026-01-01 | 35 | After Round 13 (-9 axioms) |
| 2026-01-01 | 32 | After Round 14 (-3 axioms) |
| | | |

---

## References

- Hodge-v6-w-Jon-Update-MERGED.tex (the paper)
- Harvey-Lawson, Acta Math. 148 (1982)
- Federer-Fleming, Ann. Math. 72 (1960)
- Serre, Ann. Inst. Fourier 6 (1956)
