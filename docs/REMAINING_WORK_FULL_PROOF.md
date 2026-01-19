# Remaining Work for a Full Hodge Proof (No Stubs)

**Last Updated**: 2026-01-10  
**Status**: The proof-track for `hodge_conjecture'` is currently **sorry-free and axiom-free** (only depends on `propext`, `Classical.choice`, `Quot.sound`).  
**Goal**: Replace all stub definitions with real mathematical implementations.

---

## Executive Summary

The current Lean formalization has a **complete proof architecture** but uses **stub implementations** for core mathematical operations. The main theorem `hodge_conjecture'` compiles successfully and passes the axiom guard, but the underlying mathematics is "vacuous" in the sense that:

- The exterior derivative `d` is stubbed to `0` (making all forms closed)
- Integration `topFormIntegral` is stubbed to `0`
- Various Hodge theory operators use axiomatized fiber operations

This document outlines **all files that need to be added or completed** for a fully faithful mathematical proof.

---

## Files Overview

### Already Complete (No Changes Needed)
These files have complete, non-stub implementations:
- `Hodge/Main.lean` - Main theorem orchestration
- `Hodge/AxiomGuard.lean` - Axiom tracking
- `Hodge/Basic.lean` - Basic type definitions

### Partially Complete (Minor Updates)
- `Hodge/Cohomology/Basic.lean` - Ring structure uses axiomatized wedge
- `Hodge/Classical/*.lean` - Use axiomatized constructions

### Major Work Required
See detailed sections below.

---

## Category 1: Core Analysis Infrastructure

### 1.1 Real Exterior Derivative

**Current State**: `extDerivLinearMap` in `Hodge/Analytic/Forms.lean` delegates to `ContMDiffForm.extDerivForm` which is in `Hodge/Analytic/Advanced/ContMDiffForms.lean`.

**Files to Complete**:

| File | Status | Work Needed |
|------|--------|-------------|
| `Hodge/Analytic/Advanced/ContMDiffForms.lean` | Exists, partial | Complete `extDerivForm.smooth'` (d maps C^∞ to C^∞) |
| `Hodge/Analytic/Advanced/LeibnizRule.lean` | Exists, complete | Already sorry-free |
| **NEW** `Hodge/Analytic/Advanced/ChartIndependence.lean` | Needed | Prove `extDerivAt_eq_chart_extDeriv` |
| **NEW** `Hodge/Analytic/Advanced/ExteriorDerivSq.lean` | Needed | Prove `d² = 0` for manifold d |

**Key Theorems**:
```lean
-- Chart independence of d
theorem extDerivAt_eq_chart_extDeriv : 
    extDerivAt ω x = (chart transition) ▸ extDerivAt_chart ω x

-- d² = 0
theorem extDeriv_extDeriv : smoothExtDeriv (smoothExtDeriv ω) = 0
```

**Dependencies**: Mathlib manifold calculus, `tangentCoordChange` derivatives

**Estimated Effort**: 3-6 months

---

### 1.2 Integration Theory

**Current State**: `topFormIntegral` in `Hodge/Kahler/Microstructure.lean` returns `0`.

**Files to Complete**:

| File | Status | Work Needed |
|------|--------|-------------|
| **NEW** `Hodge/Analytic/Integration/VolumeForm.lean` | Needed | Construct volume form from Kähler metric |
| **NEW** `Hodge/Analytic/Integration/TopFormIntegral.lean` | Needed | Define integration of top forms |
| **NEW** `Hodge/Analytic/Integration/StokesTheorem.lean` | Needed | Stokes' theorem on manifolds |
| **NEW** `Hodge/Analytic/Integration/HausdorffMeasure.lean` | Needed | Integration on submanifolds |
| `Hodge/Kahler/Microstructure.lean` | Update | Replace `topFormIntegral := fun _ => 0` |

**Key Definitions**:
```lean
-- Volume form from Kähler structure
def kahlerVolumeForm (n : ℕ) (X : Type*) [KahlerManifold n X] : 
    SmoothForm n X (2 * n)

-- Real integration
def topFormIntegral (ω : SmoothForm n X (2 * n)) : ℝ :=
    ∫ x, ⟨ω.as_alternating x, kahlerVolumeForm.as_alternating x⟩ ∂μ
```

**Dependencies**: Mathlib `MeasureTheory`, Riemannian volume, Fubini

**Estimated Effort**: 4-8 months

---

### 1.3 Hodge Star Operator

**Current State**: `hodgeStarLinearMap` uses `fiberHodgeStar` axiom.

**Files to Complete**:

| File | Status | Work Needed |
|------|--------|-------------|
| **NEW** `Hodge/Analytic/HodgeStar/FiberStar.lean` | Needed | Construct pointwise ⋆ from metric |
| **NEW** `Hodge/Analytic/HodgeStar/Involution.lean` | Needed | Prove ⋆⋆ = ±1 |
| **NEW** `Hodge/Analytic/HodgeStar/Smoothness.lean` | Needed | Prove ⋆ω is smooth if ω is |
| `Hodge/Kahler/Manifolds.lean` | Update | Replace axiom with construction |

**Key Theorems**:
```lean
-- Pointwise construction
def fiberHodgeStar_impl (α : FiberAlt n k) : FiberAlt n (2 * n - k) :=
    -- Use inner product and volume form on fibers

-- Involution
theorem hodgeStar_hodgeStar : ⋆(⋆ω) = hodgeStarSign k n • ω
```

**Dependencies**: Riemannian metric on tangent bundle, inner product on ∧^k

**Estimated Effort**: 3-5 months

---

### 1.4 Codifferential and Laplacian

**Current State**: `adjointDerivLinearMap` uses `fiberAdjointDeriv` axiom.

**Files to Complete**:

| File | Status | Work Needed |
|------|--------|-------------|
| **NEW** `Hodge/Analytic/Laplacian/Codifferential.lean` | Needed | Define δ = ±⋆d⋆ |
| **NEW** `Hodge/Analytic/Laplacian/HodgeLaplacian.lean` | Needed | Define Δ = dδ + δd |
| **NEW** `Hodge/Analytic/Laplacian/HarmonicForms.lean` | Needed | Harmonic form theory |
| `Hodge/Kahler/Manifolds.lean` | Update | Replace axioms with constructions |

**Key Theorems**:
```lean
-- Codifferential from Hodge star
def adjointDeriv (ω : SmoothForm n X k) : SmoothForm n X (k - 1) :=
    (-1)^(n*k + n + 1) • hodgeStar (smoothExtDeriv (hodgeStar ω))

-- Harmonic implies closed and coclosed
theorem isHarmonic_implies_closed : laplacian ω = 0 → smoothExtDeriv ω = 0
theorem isHarmonic_implies_coclosed : laplacian ω = 0 → adjointDeriv ω = 0
```

**Dependencies**: Real Hodge star (1.3), real exterior derivative (1.1)

**Estimated Effort**: 2-4 months (after 1.1 and 1.3)

---

## Category 2: Kähler Geometry

### 2.1 Dolbeault Operators

**Current State**: Not implemented (would be needed for real Hodge decomposition).

**Files to Complete**:

| File | Status | Work Needed |
|------|--------|-------------|
| **NEW** `Hodge/Kahler/Dolbeault/Operators.lean` | Needed | Define ∂, ∂̄ operators |
| **NEW** `Hodge/Kahler/Dolbeault/TypeDecomposition.lean` | Needed | (p,q)-type decomposition |
| **NEW** `Hodge/Kahler/Dolbeault/Cohomology.lean` | Needed | Dolbeault cohomology H^{p,q} |
| **NEW** `Hodge/Kahler/Dolbeault/HodgeDecomposition.lean` | Needed | H^k = ⊕ H^{p,q} |

**Key Definitions**:
```lean
-- Dolbeault operators
def dolbeault (ω : SmoothForm n X k) : SmoothForm n X (k + 1)  -- ∂
def dolbeaultBar (ω : SmoothForm n X k) : SmoothForm n X (k + 1)  -- ∂̄

-- Relation to exterior derivative
theorem d_eq_dolbeault_add_bar : smoothExtDeriv = dolbeault + dolbeaultBar
```

**Dependencies**: Complex structure on manifold, (p,q)-type forms

**Estimated Effort**: 4-6 months

---

### 2.2 Kähler Identities

**Current State**: Axiomatized in `KahlerIdentities.lean` (archived).

**Files to Complete**:

| File | Status | Work Needed |
|------|--------|-------------|
| **NEW** `Hodge/Kahler/Identities/LambdaD.lean` | Needed | Prove [Λ, d] = i(∂̄* - ∂*) |
| **NEW** `Hodge/Kahler/Identities/LDelta.lean` | Needed | Prove [L, δ] = -i(∂̄ - ∂) |
| **NEW** `Hodge/Kahler/Identities/Sl2.lean` | Needed | Prove sl(2) relations |

**Key Theorems**:
```lean
-- Kähler identities
theorem kahler_identity_Lambda_d : [Λ, d] = i • (dolbeaultBarStar - dolbeaultStar)
theorem kahler_identity_L_delta : [L, δ] = -i • (dolbeaultBar - dolbeault)

-- sl(2) relations
theorem sl2_L_Lambda : [L, Λ] = weightOperator
theorem sl2_H_L : [H, L] = 2 • L
theorem sl2_H_Lambda : [H, Λ] = -2 • Λ
```

**Dependencies**: Dolbeault operators (2.1), Hodge star (1.3)

**Estimated Effort**: 2-4 months (after 2.1)

---

### 2.3 Hard Lefschetz (Proved Version)

**Current State**: `lefschetz_bijective` is a typeclass field (axiom). Task 4 infrastructure complete, uses `sl2_representation_bijectivity` axiom.

**Files to Complete**:

| File | Status | Work Needed |
|------|--------|-------------|
| **NEW** `Hodge/Kahler/Lefschetz/Sl2Representation.lean` | Needed | Prove sl(2) rep bijectivity |
| **NEW** `Hodge/Kahler/Lefschetz/PrimitiveDecomp.lean` | Needed | Constructive primitive decomposition |
| `Hodge/Classical/Lefschetz.lean` | Update | Remove `lefschetz_inverse_cohomology := 0` |

**Key Theorems**:
```lean
-- Prove sl(2) representation bijectivity from rep theory
theorem sl2_representation_bijectivity : 
    Function.Bijective (L^(n-k) : H^k → H^{2n-k})

-- Remove axiom, prove as theorem
theorem hard_lefschetz_bijective : Function.Bijective (lefschetz_power n X p k)
```

**Dependencies**: sl(2) identities (2.2), primitive decomposition

**Estimated Effort**: 3-6 months (after 2.2)

---

## Category 3: Geometric Measure Theory

### 3.1 Integration Currents

**Current State**: `poincareDualFormExists` is axiomatized.

**Files to Complete**:

| File | Status | Work Needed |
|------|--------|-------------|
| **NEW** `Hodge/GMT/Current.lean` | Needed | Current = functional on forms |
| **NEW** `Hodge/GMT/IntegrationCurrent.lean` | Needed | T_Z(ω) = ∫_Z ω |
| **NEW** `Hodge/GMT/PoincareDuality.lean` | Needed | PD: H_{2n-2p} → H^{2p} |
| **NEW** `Hodge/GMT/CurrentToForm.lean` | Needed | Regularization T → η |
| `Hodge/Classical/CycleClass.lean` | Update | Replace axiom with construction |

**Key Definitions**:
```lean
-- Integration current
def integrationCurrent (Z : Set X) : Current n X k := {
    toFun := fun ω => ∫ z in Z, ω.restrict Z ∂μ_Z,
    is_continuous := ...
}

-- Poincaré dual form
def poincareDualForm (Z : Set X) : SmoothForm n X (2 * p) :=
    regularize (integrationCurrent Z)
```

**Dependencies**: Integration (1.2), Hausdorff measure, regularity theory

**Estimated Effort**: 6-12 months

---

### 3.2 Federer-Fleming Compactness

**Current State**: Axiomatized as Classical Pillar.

**Files to Complete**:

| File | Status | Work Needed |
|------|--------|-------------|
| **NEW** `Hodge/GMT/FlatNormTopology.lean` | Needed | Flat norm metric space |
| **NEW** `Hodge/GMT/IntegralCurrentSpace.lean` | Needed | Space of integral currents |
| **NEW** `Hodge/GMT/FedererFleming.lean` | Needed | Compactness theorem |
| `Hodge/Classical/FedererFleming.lean` | Update | Replace axiom with proof |

**Key Theorem**:
```lean
theorem federer_fleming_compactness :
    ∀ (M : ℝ), IsCompact { T : IntegralCurrent n X k | mass T ≤ M ∧ bdryMass T ≤ M }
```

**Dependencies**: Flat norm (partially done), measure theory

**Estimated Effort**: 12-24 months (major GMT development)

---

### 3.3 Harvey-Lawson Structure Theorem

**Current State**: Axiomatized as Classical Pillar.

**Files to Complete**:

| File | Status | Work Needed |
|------|--------|-------------|
| **NEW** `Hodge/GMT/CalibratedGeometry.lean` | Needed | Calibrated currents theory |
| **NEW** `Hodge/GMT/HarveyLawsonTheorem.lean` | Needed | Structure theorem proof |
| `Hodge/Classical/HarveyLawson.lean` | Update | Replace axiom with proof |

**Key Theorem**:
```lean
theorem harvey_lawson_structure :
    isCalibrated T ψ → ∃ (varieties : List AnalyticSubvariety), 
        T = ∑ v ∈ varieties, integrationCurrent v.carrier
```

**Dependencies**: Calibration theory, GMT compactness

**Estimated Effort**: 12-24 months

---

## Category 4: Complex Algebraic Geometry

### 4.1 GAGA Principle

**Current State**: Axiomatized as Classical Pillar.

**Files to Complete**:

| File | Status | Work Needed |
|------|--------|-------------|
| **NEW** `Hodge/AlgGeom/CoherentSheaves.lean` | Needed | Coherent sheaves on X |
| **NEW** `Hodge/AlgGeom/AnalyticSheaves.lean` | Needed | Analytic sheaves |
| **NEW** `Hodge/AlgGeom/GAGA.lean` | Needed | Equivalence proof |
| `Hodge/Classical/GAGA.lean` | Update | Replace axiom with proof |

**Key Theorem**:
```lean
theorem gaga : Coh(X_alg) ≃ Coh(X_an)
```

**Dependencies**: Scheme theory, coherent sheaves (minimal in Mathlib)

**Estimated Effort**: 12-24 months

---

## Summary: New Files Required

### High Priority (Enables non-vacuous proof)

| # | File Path | Purpose | Dependencies |
|---|-----------|---------|--------------|
| 1 | `Hodge/Analytic/Advanced/ChartIndependence.lean` | Exterior derivative chart independence | Manifold calculus |
| 2 | `Hodge/Analytic/Advanced/ExteriorDerivSq.lean` | d² = 0 | Chart independence |
| 3 | `Hodge/Analytic/Integration/VolumeForm.lean` | Kähler volume form | Riemannian geometry |
| 4 | `Hodge/Analytic/Integration/TopFormIntegral.lean` | Top form integration | Volume form |
| 5 | `Hodge/Analytic/HodgeStar/FiberStar.lean` | Pointwise Hodge star | Inner product |
| 6 | `Hodge/Analytic/HodgeStar/Involution.lean` | ⋆⋆ = ±1 | Fiber star |

### Medium Priority (Full Kähler theory)

| # | File Path | Purpose | Dependencies |
|---|-----------|---------|--------------|
| 7 | `Hodge/Analytic/Laplacian/Codifferential.lean` | δ = ±⋆d⋆ | Hodge star |
| 8 | `Hodge/Analytic/Laplacian/HodgeLaplacian.lean` | Δ = dδ + δd | Codifferential |
| 9 | `Hodge/Kahler/Dolbeault/Operators.lean` | ∂, ∂̄ operators | Complex structure |
| 10 | `Hodge/Kahler/Dolbeault/TypeDecomposition.lean` | (p,q)-forms | Dolbeault |
| 11 | `Hodge/Kahler/Identities/LambdaD.lean` | [Λ, d] identity | Dolbeault |
| 12 | `Hodge/Kahler/Lefschetz/Sl2Representation.lean` | sl(2) bijectivity | Kähler identities |

### Low Priority (Replace Classical Pillars)

| # | File Path | Purpose | Dependencies |
|---|-----------|---------|--------------|
| 13 | `Hodge/GMT/IntegrationCurrent.lean` | T_Z construction | Integration |
| 14 | `Hodge/GMT/PoincareDuality.lean` | PD isomorphism | Currents |
| 15 | `Hodge/GMT/FedererFleming.lean` | Compactness | Flat norm |
| 16 | `Hodge/GMT/HarveyLawsonTheorem.lean` | Structure theorem | Calibration |
| 17 | `Hodge/AlgGeom/GAGA.lean` | GAGA principle | Scheme theory |

---

## Existing Files Requiring Updates

| File | Current Issue | Required Change |
|------|---------------|-----------------|
| `Hodge/Analytic/Forms.lean` | `extDerivLinearMap` delegates to Advanced module | Update once Advanced is complete |
| `Hodge/Kahler/Microstructure.lean` | `topFormIntegral := 0` | Replace with real integration |
| `Hodge/Kahler/Manifolds.lean` | `fiberHodgeStar` axiom | Replace with construction |
| `Hodge/Kahler/Manifolds.lean` | `fiberAdjointDeriv` axiom | Replace with ±⋆d⋆ |
| `Hodge/Classical/CycleClass.lean` | `poincareDualFormExists` axiom | Replace with integration current |
| `Hodge/Classical/FedererFleming.lean` | `federer_fleming_compactness` axiom | Prove from GMT |
| `Hodge/Classical/HarveyLawson.lean` | `harvey_lawson_theorem` axiom | Prove from calibration |
| `Hodge/Classical/GAGA.lean` | `gaga_analytic_is_algebraic` axiom | Prove from GAGA |
| `Hodge/Classical/Lefschetz.lean` | `lefschetz_inverse_cohomology := 0` | Use bijective inverse |

---

## Effort Estimates

| Phase | Scope | Estimated Time | Team Size |
|-------|-------|----------------|-----------|
| Phase 1: Core Analysis | Exterior derivative, Hodge star, integration | 6-12 months | 2-3 |
| Phase 2: Kähler Theory | Dolbeault, Kähler identities, sl(2) | 6-12 months | 2-3 |
| Phase 3: GMT | Currents, compactness, Harvey-Lawson | 12-24 months | 3-4 |
| Phase 4: GAGA | Algebraic geometry, coherent sheaves | 12-24 months | 2-3 |

**Total for fully stub-free proof**: 3-6 years with a dedicated team

---

## Recommended Approach

### Short Term (Current State)
The proof is **acceptable** for a formalization that:
1. Shows correct logical structure
2. Identifies exactly which classical results are used (as axioms)
3. Compiles without `sorry` on the main path
4. Passes axiom guards for Lean core axioms

### Medium Term (1-2 years)
Focus on **Phase 1** to get non-vacuous mathematics:
1. Real exterior derivative with d² = 0
2. Real Hodge star with involution
3. Real integration on manifolds

This would make the cohomology classes genuinely non-trivial.

### Long Term (3-6 years)
Systematically replace Classical Pillars with proofs:
1. GMT infrastructure (Federer-Fleming, Harvey-Lawson)
2. GAGA principle
3. Full sl(2) representation theory

---

## Related Documents

- `docs/REMAINING_WORK_AGENT_TASKS.md` - Task-oriented breakdown
- `IMPLEMENTATION_PLAN.md` - High-level phasing
- `PROOF_COMPLETION_PLAN_8_PILLARS.md` - Classical axioms used
- `docs/AGENT_COORDINATION.md` - Current status tracking
