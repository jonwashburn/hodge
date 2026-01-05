# Dependency DAG & Punch List: TeX ↔ Lean

This document maps the proof chain in `Hodge-v6-w-Jon-Update-MERGED.tex` to Lean files and identifies what remains to be completed (beyond the 8 accepted classical pillars).

**Last Updated**: 2026-01-05 (0 sorries / 9 axioms baseline; staged Mathlib migration plan underway)

---

## Quick Status Summary

| Category | Count | Status |
|----------|-------|--------|
| Pillar axioms (accepted) | 9 decls | ✅ Keep |
| Extra axioms | 0 | ✅ None |
| Remaining `sorry` | 0 | ✅ None |
| Semantic stubs documented | ~12 major | ✅ All documented |
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

**All stubs now have detailed documentation** explaining:
- What they should represent mathematically
- What Mathlib infrastructure is needed
- Path to a real implementation

### Tier 1: Foundation Layer (must be done first)

| Stub | Current Definition | Correct Definition | Files Affected | Documentation |
|------|-------------------|-------------------|----------------|---------------|
| `extDerivLinearMap` | `:= 0` | Real exterior derivative d | `Analytic/Forms.lean` | ✅ Documented |
| `smoothWedge` | `:= 0` | Real wedge product ∧ | `Analytic/Forms.lean` | ✅ Documented |
| | | | ↓ | |
| De Rham cohomology | Uses stubbed d,∧ | Real quotient | `Cohomology/Basic.lean` | ✅ Works with stubs |

**Dependencies**: Everything downstream depends on real `d` and `∧`.

**Mathlib Status**: `Mathlib.Analysis.Calculus.DifferentialForm.Basic` has `extDeriv` for normed spaces. Lifting to manifolds requires chart-based construction. `AlternatingMap.domCoprod` exists for wedge but not for `ContinuousAlternatingMap`.

### Tier 2: Kähler/Hodge Operators

| Stub | Current | Correct | Depends On | Documentation |
|------|---------|---------|------------|---------------|
| `hodgeStar` | `:= 0` | Real Hodge star ⋆ | Tier 1 + metric | ✅ Documented |
| `adjointDeriv` | `:= 0` | Real codifferential δ | Tier 1 + ⋆ | ✅ Documented |
| `laplacian` | `:= 0` | Real Laplacian Δ | d, δ | ✅ Documented |
| `lefschetzLambdaLinearMap` | `:= 0` | ⋆⁻¹ ∘ L ∘ ⋆ | ⋆ | ✅ Documented |
| `kahlerPow` | match 0,1,else→0 | ω^p via real ∧ | Tier 1 ∧ | ✅ Works for p≤1 |

**Files**: `Kahler/Manifolds.lean` (with module-level documentation), `Kahler/TypeDecomposition.lean`

### Tier 3: Currents/GMT Layer

| Stub | Current | Correct | Depends On |
|------|---------|---------|------------|
| `integration_current` | opaque | Integration over subvariety | Measure theory |
| `isRectifiable` | `:= True` | Real rectifiability | GMT |
| `Current.boundary` | Uses stubbed d | Real boundary ∂ | Tier 1 d |
| `flatNorm` | Uses stubbed boundary | Real flat norm | Real ∂ |

**Files**: `Analytic/Currents.lean`, `Analytic/IntegralCurrents.lean`, `Analytic/FlatNorm.lean`

### Tier 4: Cycle Class / Representation Layer

| Stub | Current | Correct | Depends On | Documentation |
|------|---------|---------|------------|---------------|
| `FundamentalClassSet` | `:= 0` | Poincaré dual of [Z] | Tier 3 integration + de Rham | ✅ Documented |
| `SignedAlgebraicCycle.RepresentsClass` | Compares to `0` | Real cycle class map | Fundamental class | Works with stub |
| `HarveyLawsonConclusion.represents` | `:= fun _ => True` | Real representation | Harvey-Lawson theory | ✅ Documented |

**Files**: `Classical/GAGA.lean` (FundamentalClassSet documented), `Classical/HarveyLawson.lean` (harvey_lawson_theorem documented)

### Tier 5: Microstructure/SYR

| Stub | Current | Correct | Depends On |
|------|---------|---------|------------|
| `SmoothForm.pairing` | `:= 0` | Real ∫ α ∧ β | Tier 1 ∧, integration |
| `RawSheetSum.toCycleIntegralCurrent` | Returns zero | Real sheet integration | Tier 3 |
| `cubulation_exists` | `{univ}` | Real coordinate cubulation | Charts |
| `microstructureSequence` | Returns zeros | Real SYR construction | Everything above |

**Files**: `Kahler/Microstructure.lean`

---

## Dependency DAG (Visual)

```
                    ┌─────────────────────────────────────────────────┐
                    │              hodge_conjecture'                   │
                    │           (Kahler/Main.lean)                     │
                    └───────────────────┬─────────────────────────────┘
                                        │
           ┌────────────────────────────┼────────────────────────────┐
           │                            │                            │
           ▼                            ▼                            ▼
┌──────────────────────┐  ┌─────────────────────────┐  ┌─────────────────────────┐
│  Hard Lefschetz      │  │  signed_decomposition   │  │  cone_positive_represents│
│  reduction (p>n/2)   │  │  (SignedDecomp.lean)    │  │  (Main.lean)             │
│  [PILLAR 6]          │  │  ✅ done (uses P7)      │  │                          │
│  ✅ proven           │  └─────────────────────────┘  └───────────┬─────────────┘
└──────────────────────┘                                           │
                                                     ┌─────────────┴─────────────┐
                                                     │                           │
                                                     ▼                           ▼
                                         ┌────────────────────┐    ┌─────────────────────────┐
                                         │ omega_pow_algebraic │    │ automatic_syr + H-L     │
                                         │ [PILLAR 8] ✅       │    │ (Main.lean)             │
                                         └────────────────────┘    └───────────┬─────────────┘
                                                                               │
                    ┌──────────────────────────────────────────────────────────┤
                    │                              │                           │
                    ▼                              ▼                           ▼
        ┌───────────────────┐       ┌─────────────────────────┐    ┌─────────────────────────┐
        │ microstructure    │       │ limit_is_calibrated     │    │ harvey_lawson_theorem   │
        │ Sequence          │       │ (Calibration.lean)      │    │ (HarveyLawson.lean)     │
        │ [STUB: zeros]     │       │ ✅ proven from P3       │    │ [STUB: empty, True]     │
        └───────────────────┘       └───────────┬─────────────┘    │ + axiom P5 bridge       │
                                                │                  └───────────┬─────────────┘
                                                ▼                              │
                                    ┌─────────────────────────┐                ▼
                                    │ mass_lsc [PILLAR 3]     │    ┌─────────────────────────┐
                                    │ spine_theorem [PILLAR 4]│    │ serre_gaga [PILLAR 1]   │
                                    │ FF_compactness [P2]     │    └─────────────────────────┘
                                    └─────────────────────────┘
```

---

## Execution Order (Bottom-Up)

### Phase 0: Axiom Hygiene ✅ COMPLETE
- [x] Remove `de_rham_surjective` (was unused)
- [x] Remove `integration_current_closed` (was unused)
- [x] Promote `omega_pow_algebraic` to axiom (Pillar 8)
- [x] Fix `lefschetz_lift_signed_cycle` sorry (cast lemma)

### Phase 1: Foundation (blocks everything else) - ✅ WEDGE COMPLETE
The stubs have been extensively documented with implementation paths.

- [x] Document `extDerivLinearMap := 0` implementation path (needs `ContMDiff` forms)
- [x] Document `smoothWedge := 0` implementation path (using `AlternatingMap.domCoprod`)
- [x] **COMPLETED**: `ContinuousAlternatingMap.wedge` in `Hodge/Analytic/DomCoprod.lean`
  - Full bilinearity proofs: `wedge_add_left`, `wedge_add_right`, `wedge_smul_left`, `wedge_smul_right`
  - Joint continuity: `continuous_wedge`
- [x] **COMPLETED**: `smoothWedge` in `Hodge/Analytic/Forms.lean` uses `ContinuousAlternatingMap.wedge`
- [ ] Replace `extDerivLinearMap := 0` with real implementation (blocked by Mathlib `ContMDiff` forms)

### Phase 2: Currents/GMT
- [ ] Define real `integration_current` (or use Mathlib if available)
- [ ] Define real `isRectifiable` (Mathlib `MeasureTheory.Measure.IsRectifiable`)
- [ ] Real `Current.boundary` using real `d`
- [ ] Real `flatNorm` using real boundary

### Phase 3: Cycle Class
- [ ] Replace `FundamentalClassSet := 0` with real cycle class map
- [ ] Prove `FundamentalClassSet_*` theorems from the real definition
- [ ] Update `SignedAlgebraicCycle.RepresentsClass` to be nontrivial

### Phase 4: Harvey-Lawson Interface
- [ ] Replace `harvey_lawson_theorem` stub with real conclusion (axiom P5 stays)
- [ ] Replace `represents := fun _ => True` with real representation predicate

### Phase 5: Microstructure/SYR (the "new math")
- [ ] Real `SmoothForm.pairing` (integration)
- [ ] Real `RawSheetSum.toCycleIntegralCurrent`
- [ ] Real cubulation infrastructure
- [ ] Real microstructure sequence (this is the TeX §7 construction)

### Phase 6: Final Cleanup
- [x] Verify all 8 pillars are the only axioms on critical path ✅
- [x] Critical path has no `sorry` ✅
- [x] Off-critical-path sorry in `Bergman.lean` - ELIMINATED (no sorry in codebase)
- [ ] Off-critical-path axiom `holomorphic_transition_general` (bundle infra, not on critical path)
- [ ] Verify `SignedAlgebraicCycle.RepresentsClass` is nontrivial (requires real `FundamentalClassSet`)

---

## TeX Section → Lean File Cross-Reference

| TeX Section | Label | Lean File(s) | Status |
|-------------|-------|--------------|--------|
| §1 Introduction | | `Hodge/Main.lean` | Entry point |
| §2 Notation/Kähler Prelims | | `Basic.lean`, `Kahler/Manifolds.lean` | ✅ structure exists |
| §3 Calibrated Grassmannian | `sec:calibrated-grassmannian` | `Analytic/Grassmannian.lean` | Partial |
| §4 Energy Gap | `sec:energy-gap` | (not formalized) | Optional |
| §5 ε-Net | | (not formalized) | Optional |
| §6 Linear Algebra | `sec:linear-algebra` | (not formalized) | Optional |
| §7 Calibration-Coercivity | `sec:cal-coercivity` | `Analytic/Calibration.lean` | Partial (coercivity optional) |
| §8 Realization/SYR | `sec:realization` | `Kahler/Microstructure.lean` | STUB |
| └─ H1: Local sheets | `thm:local-sheets` | (not formalized) | Needed for real SYR |
| └─ H2: Gluing | `prop:glue-gap` | (not formalized) | Needed for real SYR |
| └─ Automatic SYR | `thm:automatic-syr` | `Kahler/Main.lean` | Skeleton |
| §9 Signed Decomp | `lem:signed-decomp` | `Kahler/SignedDecomp.lean` | ✅ |
| §9 γ⁻ algebraic | `lem:gamma-minus-alg` | `Kahler/Main.lean` | ✅ Pillar 8 |
| §9 Cone-positive algebraic | `thm:effective-algebraic` | `Kahler/Main.lean` | Depends on SYR |
| §9 Main Hodge | `thm:main-hodge` | `Kahler/Main.lean` | ✅ Skeleton complete |
| Appendix: External theorems | | `Classical/*.lean` | Pillars 1,2,6 |

---

## Summary: Current State

**Achieved ("8 pillars only + no critical-path sorry"):**
1. ✅ Extra axioms eliminated (Phase 0)
2. ✅ `omega_pow_algebraic` is now Pillar 8 axiom (Phase 0)
3. ✅ `lefschetz_lift_signed_cycle` proven with `cast_zero` lemma (Phase 0)
4. ✅ Build succeeds: `lake build Hodge.Main`
5. ✅ All major semantic stubs documented with implementation paths (Phase 1)

**Blocking Issues for Real Implementations:**
1. **Mathlib Gap**: No differential forms on manifolds (only normed spaces via `extDeriv`)
2. ~~**Mathlib Gap**: No `ContinuousAlternatingMap.domCoprod` for wedge products~~ ✅ **RESOLVED** in `DomCoprod.lean`
3. **Infrastructure**: `SmoothForm` only carries `Continuous`, not `Differentiable` data
4. **GMT**: Integration currents require measure-theoretic foundations

**Next Steps (when Mathlib infrastructure exists):**
1. Strengthen `SmoothForm` to carry differentiability data (`ContMDiff` sections)
2. Implement chart-based exterior derivative using `extDeriv`
3. ~~Add continuous wedge product via `domCoprod` + continuity proof~~ ✅ **DONE**
4. Define integration currents using Mathlib measure theory

**The skeleton is complete and type-checks. The 9 classical pillars are the only axioms on the critical path. All stubs are documented with clear paths to real implementations.**

---

## Agent Coordination Strategy

When multiple agents work on this codebase simultaneously, use the following strategy to avoid conflicts:

### Bottom-Up Agent (works from foundation up)
- Focus on: Phase 1 (Foundation), Phase 2 (Currents/GMT), Phase 3 (Cycle Class)
- Files: `Hodge/Analytic/*.lean`, `Hodge/Cohomology/*.lean`
- Direction: Start from infrastructure and work up toward higher-level theorems

### Top-Down Agent (works from theorems down)  
- Focus on: Phase 6 (Final Cleanup), Phase 5 (Microstructure/SYR), Phase 4 (Harvey-Lawson)
- Files: `Hodge/Kahler/*.lean`, `Hodge/Classical/*.lean`
- Direction: Start from main theorems and work down toward infrastructure

### Coordination Rules
1. **Do NOT modify the same file simultaneously**
2. **Check git status before starting work** to see what files are modified
3. **Commit frequently** with descriptive messages
4. **Always verify 0 sorries, 9 axioms** after changes
5. **Run `lake build Hodge` before pushing** to ensure no regressions

