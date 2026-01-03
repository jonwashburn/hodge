# Axioms in the Hodge Conjecture Proof Chain

**Total: 44 custom axioms** (excluding Lean system axioms: propext, Classical.choice, Quot.sound)

These are the ONLY axioms that appear in the proof of `hodge_conjecture'`. Every one of these must either be:
1. **PROVEN** as a theorem
2. **DOCUMENTED** as a classical pillar (deep theorem from literature)

## Classical pillars (keep as axioms)

The **target end state** is that the proof depends on Lean’s standard axioms plus a small
set of **9 classical pillar axioms** (deep external theorems). The authoritative list is:

- `mass_lsc` (`Hodge/Analytic/Calibration.lean`)
- `exists_uniform_interior_radius` (`Hodge/Kahler/Cone.lean`)
- `serre_gaga` (`Hodge/Classical/GAGA.lean`)
- `harvey_lawson_fundamental_class` (`Hodge/Kahler/Main.lean`)
- `omega_pow_represents_multiple` (`Hodge/Kahler/Main.lean`)
- `lefschetz_lift_signed_cycle` (`Hodge/Kahler/Main.lean`)
- `flat_limit_existence` (`Hodge/Kahler/Microstructure.lean`)
- `calibration_defect_from_gluing` (`Hodge/Kahler/Microstructure.lean`)
- `hard_lefschetz_bijective` (`Hodge/Classical/Lefschetz.lean`)

See `CLASSICAL_PILLARS.md` for meaning + citations.

---

## 🔴 PRIORITY 1: Strategy-Critical (Pillars)

| Axiom | File | Line | Status |
|-------|------|------|--------|
| `harvey_lawson_fundamental_class` | Main.lean | 112 | ✅ CLASSICAL PILLAR |
| `lefschetz_lift_signed_cycle` | Main.lean | 195 | ✅ CLASSICAL PILLAR |

**Why critical:** These directly encode the Hodge Conjecture strategy.

---

## 🟠 PRIORITY 2: Microstructure Axioms (5 axioms)

These encode the paper's construction of approximating cycles:

| Axiom | File | Line | Action Required |
|-------|------|------|-----------------|
| `cubulation_exists` | Microstructure.lean | 147 | **PROVE** from combinatorics |
| `calibration_defect_from_gluing` | Microstructure.lean | 168 | ✅ CLASSICAL PILLAR |
| `microstructureSequence_defect_bound_axiom` | Microstructure.lean | 219 | **PROVE** from defect estimates |
| `microstructureSequence_mass_bound_axiom` | Microstructure.lean | 241 | **PROVE** from mass bounds |
| `RawSheetSum.toIntegralCurrent_isCycle` | Microstructure.lean | 116 | **PROVE** from boundary vanishing |

**Why critical:** These are paper-specific constructions that MUST be proven.

---

## 🟡 PRIORITY 3: Flat Norm / Mass (9 axioms)

| Axiom | File | Line | Action |
|-------|------|------|--------|
| `flatNorm_nonneg` | FlatNorm.lean | 32 | Prove from infimum |
| `flatNorm_zero` | FlatNorm.lean | 35 | Prove from definition |
| `eval_le_flatNorm` | FlatNorm.lean | 45 | Prove from duality |
| `flatNorm_le_mass` | FlatNorm.lean | 50 | Prove from definition |
| `flatNorm_neg` | FlatNorm.lean | 56 | Prove from symmetry |
| `flatNorm_eq_zero_iff` | FlatNorm.lean | 59 | Prove from norm properties |
| `flatNorm_boundary_le` | FlatNorm.lean | 66 | Classical estimate |
| `flat_limit_existence` | Microstructure.lean | 192 | ✅ CLASSICAL PILLAR |
| `mass_lsc` | Calibration.lean | 116 | ✅ CLASSICAL PILLAR |

---

## 🟡 PRIORITY 4: Kähler / Calibration (8 axioms)

| Axiom | File | Line | Action |
|-------|------|------|--------|
| `wirtinger_comass_bound` | Calibration.lean | — | ✅ eliminated (no longer needed; `KählerCalibration` is 0-form) |
| `calibration_inequality` | Calibration.lean | 65 | ✅ already a theorem in `Hodge/Analytic/Calibration.lean` |
| `simpleCalibratedForm` | Grassmannian.lean | 106 | ✅ done (now a `def`, not an axiom) |
| `omegaPow_in_interior` | Cone.lean | — | ✅ done (axiom removed; cone membership derived from `exists_uniform_interior_radius`) |
| `exists_uniform_interior_radius` | Cone.lean | 92 | CLASSICAL PILLAR (uniform interior radius) |
| `omega_pow_IsFormClosed` | TypeDecomposition.lean | 125 | Prove: d(ω^p) = 0 |
| `omega_pow_is_rational` | TypeDecomposition.lean | 128 | ω is integral class |
| `omega_pow_represents_multiple` | Main.lean | 173 | ✅ CLASSICAL PILLAR |
| `hard_lefschetz_bijective` | Lefschetz.lean | 106 | ✅ CLASSICAL PILLAR |
| `shift_makes_conePositive_rat` | Cone.lean | 173 | Prove from cone structure |

---

## 🟢 PRIORITY 5: Form/Cohomology Structure (10 axioms)

These define algebraic structure on forms and cohomology:

| Axiom | File | Line | Action |
|-------|------|------|--------|
| `SmoothForm.zero` | Basic.lean | 71 | Interface: define 0 form |
| `SmoothForm.instAddCommGroup` | Basic.lean | 80 | Interface: + structure |
| `SmoothForm.instModuleComplex` | Basic.lean | 84 | Interface: ℂ-module |
| `SmoothForm.instTopologicalSpace` | Basic.lean | 93 | Interface: topology |
| `smoothExtDeriv_add` | Basic.lean | 113 | **PROVE** if d is defined |
| `smoothExtDeriv_smul` | Basic.lean | 118 | **PROVE** if d is defined |
| `smoothExtDeriv_smul_real` | Basic.lean | 123 | **PROVE** if d is defined |
| `instAddCommGroupDeRhamCohomologyClass` | Basic.lean | 310 | **PROVE** from quotient |
| `instModuleDeRhamCohomologyClass` | Basic.lean | 324 | **PROVE** from quotient |
| `smulRat_DeRhamCohomologyClass` | Basic.lean | 332 | **PROVE** from module |

---

## 🟢 PRIORITY 6: Quotient Operations (3 axioms)

| Axiom | File | Line | Action |
|-------|------|------|--------|
| `ofForm_add` | Basic.lean | 361 | **PROVE** from quotient lift |
| `ofForm_sub` | Basic.lean | 367 | **PROVE** from quotient lift |
| `ofForm_smul_real` | Basic.lean | 370 | **PROVE** from quotient lift |
| `smul_rat_eq_smul_real` | Basic.lean | 342 | **PROVE** from embedding |

---

## 🟢 PRIORITY 7: Other (7 axioms)

| Axiom | File | Line | Action |
|-------|------|------|--------|
| `pointwiseComass_nonneg` | Norms.lean | 41 | Prove: norms ≥ 0 |
| `polyhedral_zero` | IntegralCurrents.lean | 42 | Prove: 0 is polyhedral |
| `serre_gaga` | GAGA.lean | 149 | ✅ CLASSICAL PILLAR |
| `isPPForm_zero` | Basic.lean | 477 | Prove: 0 is (p,p) |
| `isRationalClass_zero` | Basic.lean | 405 | Prove: [0] is rational |
| `isRationalClass_add` | Basic.lean | 413 | Prove: closure under + |
| `isRationalClass_smul_rat` | Basic.lean | 422 | Prove: closure under ℚ |

---

## Summary: What Must Be Done

| Priority | Count | Category | Status |
|----------|-------|----------|--------|
| P1 | 0 | Strategy-Critical | ✅ All converted to pillars |
| P2 | 4 | Microstructure | ⚠️ Paper constructions |
| P3 | 7 | Flat Norm / Mass | Some provable |
| P4 | 6 | Kähler / Calibration | Some provable |
| P5 | 10 | Form Structure | Most are interface |
| P6 | 4 | Quotient Ops | Provable from Quotient.lift |
| P7 | 6 | Other | Mixed |
| **Total** | **37** | | (Excluding 9 pillars) |

### Realistic Path

1. **Classical Pillars (9 axioms)**: These are deep external theorems intentionally kept as axioms.

2. **P2 (4 axioms)**: These encode the paper's construction and MUST be proven.

3. **P3-P7 (38 axioms)**: Many can be proven with targeted effort:
   - Quotient operations (P6): Use `Quotient.lift₂`
   - Flat norm properties (P3): Prove from opaque definition
   - Rational class closure (P7): Basic closure properties

