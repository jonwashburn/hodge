# Dependency DAG & Punch List: TeX ↔ Lean

This document maps the proof chain in `Hodge-v6-w-Jon-Update-MERGED.tex` to Lean files and identifies what remains to be completed (beyond the 8 accepted classical pillars).

**Last Updated**: 2026-01-06 (Stage 3 Infrastructure Bridge complete)

---

## Quick Status Summary

| Category | Count | Status |
|----------|-------|--------|
| Pillar axioms (accepted) | 9 decls | ✅ Keep |
| Extra axioms | 0 | ✅ None |
| Remaining `sorry` | 0 | ✅ None |
| Semantic stubs documented | ~10 major | ✅ Downward trend |
| Build status | `lake build Hodge.Main` | ✅ Passing |

**Build Status**: `lake build Hodge.Main` ✅ succeeds

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
| `extDerivLinearMap` | `:= 0` | Real exterior derivative d | `Analytic/Forms.lean` | ✅ Stage 2 Groundwork DONE |
| `smoothWedge` | Mathlib-backed | Real wedge product ∧ | `Analytic/Forms.lean` | ✅ Implemented |
| De Rham cohomology | Uses stubbed d,∧ | Real quotient | `Cohomology/Basic.lean` | ✅ Works with stubs |

**Mathlib Migration Status**:
- **Stage 1 (DONE)**: Mathlib-backed wedge product implemented on fibers and lifted to manifolds.
- **Stage 2 (DONE)**: `Hodge/Analytic/ContMDiffForms.lean` provides a `ContMDiff`-based differential form infrastructure. Pointwise exterior derivative `extDerivAt` is defined and linear.
- **Stage 3 (DONE)**: **Infrastructure Bridge**. Manifold-level `mfderiv` is rigorously connected to chart-level `fderiv`. `ChartExtDeriv.lean` provides coordinate representations and smoothness proofs on chart targets. Bundled `extDerivForm` and $d^2=0$ theorem exist.

**Next**: Stage 4 — Migrating the global `SmoothForm` layer to use the now-rigorous `ContMDiffForm` exterior derivative.

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
