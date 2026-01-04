# Dependency DAG & Punch List: TeX ↔ Lean

This document maps the proof chain in `Hodge-v6-w-Jon-Update-MERGED.tex` to Lean files and identifies what remains to be completed (beyond the 8 accepted classical pillars).

---

## Quick Status Summary

| Category | Count | Status |
|----------|-------|--------|
| Pillar axioms (accepted) | 8 (in 10 `axiom` decls) | ✅ Keep |
| Extra axioms (must eliminate) | 2 | ❌ Remove |
| Remaining `sorry` | 2 | ❌ Prove |
| Semantic stubs (change meaning) | ~12 major | ❌ Replace |

---

## The 8 Classical Pillars (TeX ↔ Lean)

| # | Pillar | TeX Reference | Lean Axiom(s) | File |
|---|--------|---------------|---------------|------|
| 1 | **GAGA** | Rem. `chow-gaga`, §C.External | `serre_gaga` | `Classical/GAGA.lean` |
| 2 | **Federer-Fleming Compactness** | Thm. `realization-from-almost`, §C | `federer_fleming_compactness` | `Classical/FedererFleming.lean` |
| 3 | **Mass LSC** | Thm. `realization-from-almost` | `mass_lsc` | `Analytic/Calibration.lean` |
| 4 | **Spine / Calibration Defect** | Thm. `spine-quantitative` | `spine_theorem` | `Analytic/Calibration.lean` |
| 5 | **Harvey-Lawson** | Thm. `realization-from-almost`, Rem. `chow-gaga` | `harvey_lawson_fundamental_class` | `Kahler/Main.lean` |
| 6 | **Hard Lefschetz** | Rem. `lefschetz-reduction` | `hard_lefschetz_bijective`, `hard_lefschetz_inverse_form` | `Classical/Lefschetz.lean` |
| 7 | **Uniform Interior Radius** | Lem. `kahler-positive` | `exists_uniform_interior_radius` | `Kahler/Cone.lean` |
| 8 | **Algebraicity of ω^p** | Lem. `gamma-minus-alg` | **(currently a `sorry`)** | `Kahler/Main.lean` |

---

## TeX Proof Chain → Lean Mapping

### Main Theorem: `thm:main-hodge` (Hodge Conjecture)
**Lean**: `hodge_conjecture'` in `Hodge/Kahler/Main.lean`

```
Thm main-hodge
├── Hard Lefschetz reduction (rem:lefschetz-reduction) ──────────► Pillar 6
│   └── Lean: hard_lefschetz_bijective, hard_lefschetz_inverse_form
│       └── lefschetz_lift_signed_cycle ← SORRY (cast/transport gap)
│
├── Signed Decomposition (lem:signed-decomp) ────────────────────► ✅ DONE
│   └── Lean: SignedDecomposition, signed_decomposition
│       └── Requires: shift_makes_conePositive (proved from Pillar 7)
│
├── γ⁻ is algebraic (lem:gamma-minus-alg) ───────────────────────► Pillar 8
│   └── Lean: omega_pow_algebraic ← SORRY (p=1 case)
│       └── Needs to become a pillar axiom OR complete the proof
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

## Non-Pillar Items That Must Be Completed

### Category A: Extra Axioms to Eliminate

| Axiom | File | What's Needed |
|-------|------|---------------|
| `de_rham_surjective` | `Classical/GAGA.lean:212` | Remove (unused in proof chain) or prove from real de Rham theory |
| `integration_current_closed` | `Analytic/Currents.lean:382` | Remove (unused) or define real integration currents |

### Category B: Remaining `sorry`s

| Location | Description | Fix |
|----------|-------------|-----|
| `Kahler/Main.lean:245` | `omega_pow_algebraic` p=1 case | Either (a) promote to Pillar 8 axiom, or (b) prove using `FundamentalClassSet` = hyperplane section |
| `Kahler/Main.lean:320` | `lefschetz_lift_signed_cycle` | Prove the cast/transport lemma (zero transports to zero across degree casts) |

### Category C: Semantic Stubs (Critical Path)

These stubs make the proof type-check but don't carry the mathematical meaning of the TeX proof. They must be replaced to have a "real" formalization.

#### Tier 1: Foundation Layer (must be done first)

| Stub | Current Definition | Correct Definition | Files Affected |
|------|-------------------|-------------------|----------------|
| `extDerivLinearMap` | `:= 0` | Real exterior derivative d | `Analytic/Forms.lean` |
| `smoothWedge` | `:= 0` | Real wedge product ∧ | `Analytic/Forms.lean` |
| | | | ↓ |
| De Rham cohomology | Uses stubbed d,∧ | Real quotient | `Cohomology/Basic.lean` |

**Dependencies**: Everything downstream depends on real `d` and `∧`.

#### Tier 2: Kähler/Hodge Operators

| Stub | Current | Correct | Depends On |
|------|---------|---------|------------|
| `hodgeStar` | `:= 0` | Real Hodge star ⋆ | Tier 1 + metric |
| `adjointDeriv` | `:= 0` | Real codifferential δ | Tier 1 + ⋆ |
| `laplacian` | `:= 0` | Real Laplacian Δ | d, δ |
| `lefschetzLambdaLinearMap` | `:= 0` | ⋆⁻¹ ∘ L ∘ ⋆ | ⋆ |
| `kahlerPow` | match 0,1,else→0 | ω^p via real ∧ | Tier 1 ∧ |

**Files**: `Kahler/Manifolds.lean`, `Kahler/TypeDecomposition.lean`

#### Tier 3: Currents/GMT Layer

| Stub | Current | Correct | Depends On |
|------|---------|---------|------------|
| `integration_current` | opaque | Integration over subvariety | Measure theory |
| `isRectifiable` | `:= True` | Real rectifiability | GMT |
| `Current.boundary` | Uses stubbed d | Real boundary ∂ | Tier 1 d |
| `flatNorm` | Uses stubbed boundary | Real flat norm | Real ∂ |

**Files**: `Analytic/Currents.lean`, `Analytic/IntegralCurrents.lean`, `Analytic/FlatNorm.lean`

#### Tier 4: Cycle Class / Representation Layer

| Stub | Current | Correct | Depends On |
|------|---------|---------|------------|
| `FundamentalClassSet` | `Classical.choice ⟨0⟩` | Poincaré dual of [Z] | Tier 3 integration + de Rham |
| `SignedAlgebraicCycle.RepresentsClass` | Compares to `0` | Real cycle class map | Fundamental class |
| `HarveyLawsonConclusion.represents` | `:= fun _ => True` | Real representation | Harvey-Lawson theory |

**Files**: `Classical/GAGA.lean`, `Classical/HarveyLawson.lean`

#### Tier 5: Microstructure/SYR

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
                    │           (Kahler/Main.lean:340)                 │
                    └───────────────────┬─────────────────────────────┘
                                        │
           ┌────────────────────────────┼────────────────────────────┐
           │                            │                            │
           ▼                            ▼                            ▼
┌──────────────────────┐  ┌─────────────────────────┐  ┌─────────────────────────┐
│  Hard Lefschetz      │  │  signed_decomposition   │  │  cone_positive_represents│
│  reduction (p>n/2)   │  │  (SignedDecomp.lean)    │  │  (Main.lean:159)         │
│  [PILLAR 6]          │  │  ✅ done (uses P7)      │  │                          │
│  + sorry at :320     │  └─────────────────────────┘  └───────────┬─────────────┘
└──────────────────────┘                                           │
                                                     ┌─────────────┴─────────────┐
                                                     │                           │
                                                     ▼                           ▼
                                         ┌────────────────────┐    ┌─────────────────────────┐
                                         │ omega_pow_algebraic │    │ automatic_syr + H-L     │
                                         │ [PILLAR 8 - sorry] │    │ (Main:40-88)            │
                                         └────────────────────┘    └───────────┬─────────────┘
                                                                               │
                    ┌──────────────────────────────────────────────────────────┤
                    │                              │                           │
                    ▼                              ▼                           ▼
        ┌───────────────────┐       ┌─────────────────────────┐    ┌─────────────────────────┐
        │ microstructure    │       │ limit_is_calibrated     │    │ harvey_lawson_theorem   │
        │ Sequence          │       │ (Calibration:206)       │    │ (HarveyLawson:252)      │
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

### Phase 0: Axiom Hygiene (can do now)
- [ ] Remove `de_rham_surjective` (check if used; likely not)
- [ ] Remove `integration_current_closed` (check if used; likely not)
- [ ] Promote `omega_pow_algebraic` to `axiom` (Pillar 8) OR fix p=1 case

### Phase 1: Foundation (blocks everything else)
- [ ] Replace `extDerivLinearMap := 0` with real Mathlib exterior derivative
- [ ] Replace `smoothWedge := 0` with real Mathlib wedge product
- [ ] Update `IsFormClosed`, `IsExact`, cohomology operations

### Phase 2: Currents/GMT
- [ ] Define real `integration_current` (or use Mathlib if available)
- [ ] Define real `isRectifiable` (Mathlib `MeasureTheory.Measure.IsRectifiable`)
- [ ] Real `Current.boundary` using real `d`
- [ ] Real `flatNorm` using real boundary

### Phase 3: Cycle Class
- [ ] Replace `FundamentalClassSet := Classical.choice ⟨0⟩` with real cycle class map
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
- [ ] Prove remaining `sorry` at `lefschetz_lift_signed_cycle:320`
- [ ] Verify all 8 pillars are the only axioms
- [ ] Run `grep -R "sorry\|admit"` → empty
- [ ] Run `grep -R "^axiom"` → only 8 pillar axioms
- [ ] Verify `SignedAlgebraicCycle.RepresentsClass` is nontrivial

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
| §9 γ⁻ algebraic | `lem:gamma-minus-alg` | `Kahler/Main.lean` | sorry (P8) |
| §9 Cone-positive algebraic | `thm:effective-algebraic` | `Kahler/Main.lean` | Depends on SYR |
| §9 Main Hodge | `thm:main-hodge` | `Kahler/Main.lean` | Skeleton |
| Appendix: External theorems | | `Classical/*.lean` | Pillars 1,2,6 |

---

## Summary: What Must Be Done

**Minimal path to "8 pillars only + no sorry":**
1. Fix axiom hygiene (2 extra axioms)
2. Promote `omega_pow_algebraic` to Pillar 8 axiom (or prove p=1)
3. Prove `lefschetz_lift_signed_cycle` sorry (type cast)

**Full path to "semantically correct proof":**
1. All of the above
2. Replace `d := 0`, `∧ := 0` with real Mathlib forms
3. Replace `FundamentalClassSet := 0` with real cycle class
4. Replace `harvey_lawson_theorem` stub with real structure
5. Implement real microstructure/SYR construction

The skeleton is complete; the meaning is not yet there.

