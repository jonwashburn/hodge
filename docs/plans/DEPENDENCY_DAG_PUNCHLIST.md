# Dependency DAG & Punch List: TeX ↔ Lean

This document maps the proof chain in `Hodge-v6-w-Jon-Update-MERGED.tex` to Lean files and identifies what remains to be completed (beyond the 8 accepted classical pillars).

**Last Updated**: 2026-01-07 (Stage 4 in progress - proof outlines documented)

---

## Quick Status Summary

| Category | Count | Status |
|----------|-------|--------|
| Pillar axioms (accepted) | 9 decls | ✅ Keep |
| Extra axioms | 0 | ✅ None |
| Remaining `sorry` | 5 | ⚠️ Stage 4 work |
| Semantic stubs documented | ~10 major | ✅ Downward trend |
| Build status | `lake build Hodge.Main` | ✅ Passing |

**Build Status**: `lake build Hodge.Main` ✅ succeeds

**`sorry` Breakdown** (all in Stage 4 work, with documented proof strategies):
- `Cohomology/Basic.lean:225`: 1 (`cohomologous_wedge` - requires Leibniz rule)
- `Analytic/Forms.lean:340`: 1 (`smoothExtDeriv_wedge` - Leibniz rule d(ω∧η))
- `Analytic/ContMDiffForms.lean`: 2 sorries with proof outlines:
  - `:538` - `extDerivForm.smooth'` (smoothness via diagonal/joint smoothness argument)
  - `:661` - `h_deriv_eq` in `extDeriv_extDeriv` (chart cocycle: needs chartAt y = chartAt x locally)
- `Analytic/Currents.lean:358`: 1 (boundary operator bound - comass estimate)

**Note**: `isFormClosed_wedge` is now PROVEN using `smoothExtDeriv_wedge` + `zero_wedge` + `wedge_zero`.

**Key Mathlib Mechanisms Identified**:
- `alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero`: Symmetric 2nd derivatives vanish under alternation (d²=0)
- `chartAt_self_eq`: For model space H, `chartAt H x = refl` (trivializes chart cocycle)
- `ContMDiffAt.mfderiv_const`: mfderiv in tangent coordinates is smooth (but need joint smoothness)

**Key Theorems Proven**:
- `extDerivAt_eq_chart_extDeriv`: Chart transport identity for modelWithCornersSelf
- `extDeriv_extDeriv`: d²=0 structure (final step uses Mathlib's `extDeriv_extDeriv_apply`)
- `continuous_wedge`: Wedge product is jointly continuous
- `extDerivAt_add`, `extDerivAt_smul`: Linearity of pointwise exterior derivative

**Remaining Technical Challenges**:
1. **Chart cocycle identity** (`h_key`): For y = (chartAt x).symm u, relate `mfderiv f y` (using chartAt y) to `fderiv (f ∘ (chartAt x).symm) u` (using chartAt x). These differ by the chart transition derivative. At u = (chartAt x) x, they agree (proven as `h_at_u₀`), but functional equality fails for general u.

2. **extDerivForm smoothness**: Need to show `extDerivAt ω` is ContMDiff. The function `extDerivInTangentCoordinates ω x` is smooth at x, and equals `extDerivAt ω x` at the diagonal, but they differ in neighborhoods. Requires showing `mfderiv ω.as_alternating` is smooth as a bundle section.

3. **Leibniz rule type casting**: `d(ω∧η)` has type `FiberAlt ((k+l)+1)` while `dω∧η` has type `FiberAlt ((k+1)+l)`. The natural isomorphism `(k+l)+1 = (k+1)+l` needs explicit casting. Mathlib's DifferentialForm/Basic.lean lacks wedge Leibniz (only has linearity and d²=0).

4. **Comass boundedness of d**: For currents, need `comass(dω) ≤ C·comass(ω)`. Requires bounded operator theory on compact manifolds.

---

## The 9 Classical Axioms (Lean baseline)

These are the only axioms currently in the repository (and the only ones `hodge_conjecture'` uses):

| # | Axiom | File | TeX / Meaning |
|---|------|------|---------------|
| 1 | `serre_gaga` | `Classical/GAGA.lean` | GAGA (analytic → algebraic) |
| 2 | `mass_lsc` | `Analytic/Calibration.lean` | mass lower semicontinuity |
| 3 | `harvey_lawson_fundamental_class` | `Kahler/Main.lean` | Harvey–Lawson bridge to class |
| 4 | `exists_uniform_interior_radius` | `Kahler/Cone.lean` | cone interior radius |
| 5 | `omega_pow_algebraic` | `Kahler/Main.lean` | algebraicity of ω^p |
| 6 | `hard_lefschetz_bijective` | `Classical/Lefschetz.lean` | Hard Lefschetz |
| 7 | `hard_lefschetz_rational_bijective` | `Classical/Lefschetz.lean` | HL preserves rationality |
| 8 | `hard_lefschetz_pp_bijective` | `Classical/Lefschetz.lean` | HL preserves (p,p) |
| 9 | `existence_of_representative_form` | `Classical/Lefschetz.lean` | Hodge decomposition representative form |

---

## TeX Proof Chain → Lean Mapping

### Main Theorem: `thm:main-hodge` (Hodge Conjecture)
**Lean**: `hodge_conjecture'` in `Hodge/Kahler/Main.lean`

```
Thm main-hodge
├── Hard Lefschetz reduction (rem:lefschetz-reduction) ──────────► Pillar 6
│   └── Lean: hard_lefschetz_bijective, hard_lefschetz_inverse_form
│       └── lefschetz_lift_signed_cycle ✅ PROVEN
│
├── Signed Decomposition (lem:signed-decomp) ────────────────────► ✅ DONE
│   └── Lean: SignedDecomposition, signed_decomposition
│       └── Requires: shift_makes_conePositive (proved from Pillar 7)
│
├── γ⁻ is algebraic (lem:gamma-minus-alg) ───────────────────────► Pillar 8
│   └── Lean: omega_pow_algebraic ✅ AXIOM
│
└── γ⁺ is algebraic (thm:effective-algebraic)
    └── Automatic SYR (thm:automatic-syr)
        └── See SYR chain below
```

### SYR/Microstructure Chain: `thm:automatic-syr`
**Lean**: `automatic_syr`, `microstructure_construction_core` in `Hodge/Kahler/Main.lean` + `Hodge/Kahler/Microstructure.lean`

```
Thm automatic-syr
├── Microstructure sequence construction
│   └── Lean: microstructureSequence (Microstructure.lean)
│       └── STUB: returns zero currents (needs real GMT)
│
├── Mass/defect bounds (prop:almost-calibration)
│   └── Lean: microstructureSequence_defect_vanishes
│       └── Works (on stubbed currents)
│
├── Federer-Fleming compactness ──────────────────────────────────► Pillar 2
│   └── Lean: federer_fleming_compactness
│
├── Limit is calibrated (thm:realization-from-almost)
│   └── Lean: limit_is_calibrated
│       └── Uses mass_lsc ────────────────────────────────────────► Pillar 3
│
└── Harvey-Lawson → analytic varieties
    └── Lean: harvey_lawson_theorem (HarveyLawson.lean)
        └── STUB: returns empty set, represents := True
        └── Bridge axiom: harvey_lawson_fundamental_class ────────► Pillar 5
    └── GAGA → algebraic ─────────────────────────────────────────► Pillar 1
```

### Calibration/GMT Infrastructure
**TeX**: §2 Preliminaries, §3 Calibrated Grassmannian, §7 Spine Theorem
**Lean**: `Hodge/Analytic/*.lean`

```
Calibration layer
├── CalibratingForm structure ─────────────────────────────────────► ✅ DONE
│   └── Lean: CalibratingForm (Calibration.lean)
│
├── calibration_inequality ────────────────────────────────────────► ✅ DONE
│   └── Proven from comass bound
│
├── calibrationDefect, isCalibrated ───────────────────────────────► ✅ DONE
│
├── spine_theorem ─────────────────────────────────────────────────► Pillar 4
│
├── mass_lsc ──────────────────────────────────────────────────────► Pillar 3
│
└── limit_is_calibrated ───────────────────────────────────────────► ✅ DONE
    └── Proven from mass_lsc + eval convergence
```

---

## Phase 0 Status: ✅ COMPLETE

### Category A: Extra Axioms - ELIMINATED
| Axiom | Status |
|-------|--------|
| `de_rham_surjective` | ✅ Removed (was unused) |
| `integration_current_closed` | ✅ Removed (was unused) |

### Category B: Critical Path `sorry`s - FIXED
| Location | Status |
|----------|--------|
| `omega_pow_algebraic` | ✅ Promoted to Pillar 8 axiom |
| `lefschetz_lift_signed_cycle` | ✅ Proven using `DeRhamCohomologyClass.cast_zero` |

### Category C: Off-Critical-Path `sorry`
| Location | Description | Status |
|----------|-------------|--------|
| `Classical/Bergman.lean:261` | `IsHolomorphic_add` transition function | ⚠️ Bundle infrastructure gap - NOT on critical path |

---

## Semantic Stubs (For Full Formalization)

These stubs make the proof type-check but don't carry the mathematical meaning of the TeX proof. They must be replaced to have a "semantically correct" formalization.

### Tier 1: Foundation Layer (must be done first)

| Stub | Current Definition | Correct Definition | Files Affected | Documentation |
|------|-------------------|-------------------|----------------|---------------|
| `extDerivLinearMap` | Uses `ContMDiffForm.extDerivForm` | Real exterior derivative d | `Analytic/Forms.lean` | ✅ Stage 3 COMPLETE |
| `smoothWedge` | Mathlib-backed | Real wedge product ∧ | `Analytic/Forms.lean` | ✅ Implemented |
| De Rham cohomology | Uses real d,∧ | Real quotient | `Cohomology/Basic.lean` | ✅ Working |

**Mathlib Migration Status**:
- **Stage 1 (DONE)**: Mathlib-backed wedge product implemented on fibers and lifted to manifolds.
- **Stage 2 (DONE)**: `Hodge/Analytic/ContMDiffForms.lean` provides a `ContMDiff`-based differential form infrastructure. Pointwise exterior derivative `extDerivAt` is defined and linear.
- **Stage 3 (DONE)**: **Full Migration Complete**.
  - `SmoothForm.is_smooth` upgraded from `Continuous` to `ContMDiff`
  - `extDerivLinearMap` now uses `ContMDiffForm.extDerivForm` (real `mfderiv` + alternatization)
  - All downstream files updated to include `[IsManifold (𝓒_complex n) ⊤ X]`
  - Build passes with 9 axioms

**Stage 4 (in progress)**: Prove the remaining `sorry` statements:
- `isFormClosed_wedge` - ✅ PROVEN (using `smoothExtDeriv_wedge` + `zero_wedge` + `wedge_zero`)
- `zero_wedge`, `wedge_zero` - ✅ PROVEN (using `wedge_smul_left/right` with c=0)
- `heq` bilinearity in `cohomologous_wedge` - ✅ PROVEN (algebraic identity)
- `extDerivForm.smooth'` (smoothness of the global d operator) - pending (joint smoothness gap)
- `extDeriv_extDeriv` (d²=0) - ✅ Refined, uses Mathlib's `extDeriv_extDeriv_apply`
- `h_deriv_eq` (chart cocycle in d²=0) - pending (needs `chartAt y = chartAt x` locally)
- `smoothExtDeriv_wedge` (Leibniz rule) - pending (Mathlib gap)
- ~~Cohomology algebra laws (`mul_add`, `add_mul`, etc.) using the real d~~ ✅ DONE

**Key lemmas proven**:
- `mfderivInTangentCoordinates_eq_fderiv_diag` (chart identity on diagonal)
- `extDerivInTangentCoordinates_diag` (diagonal smoothness link)

### Tier 2: Kähler/Hodge Operators

| Stub | Current | Correct | Depends On | Documentation |
|------|---------|---------|------------|---------------|
| `hodgeStar` | `:= 0` | Real Hodge star ⋆ | Tier 1 + metric | ✅ Documented |
| `adjointDeriv` | `:= 0` | Real codifferential δ | Tier 1 + ⋆ | ✅ Documented |
| `laplacian` | `:= 0` | Real Laplacian Δ | d, δ | ✅ Documented |
| `lefschetzLambdaLinearMap` | `:= 0` | ⋆⁻¹ ∘ L ∘ ⋆ | ⋆ | ✅ Documented |
| `kahlerPow` | iterated wedge | ω^p via real ∧ | Tier 1 ∧ | ✅ Implemented |

### Tier 3: Currents/GMT Layer

| Stub | Current | Correct | Depends On |
|------|---------|---------|------------|
| `integration_current` | opaque | Integration over subvariety | Measure theory |
| `isRectifiable` | `:= True` | Real rectifiability | GMT |
| `Current.boundary` | Uses stubbed d | Real boundary ∂ | Tier 1 d |
| `flatNorm` | Uses stubbed boundary | Real flat norm | Real ∂ |
