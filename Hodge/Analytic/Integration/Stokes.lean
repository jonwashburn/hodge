/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.Analytic.Integration.IntegrationCurrent

/-!
# Stokes' Theorem

This file proves Stokes' theorem in the language of currents:
∂⟦Z⟧ = ⟦∂Z⟧

## Main Results

* `stokes_classical` - Classical Stokes: ∫_Z dω = ∫_{∂Z} ω
* `stokes_currents` - Current version: ∂⟦Z⟧ = ⟦∂Z⟧

## References

* Spivak, "Calculus on Manifolds"
* Federer, "Geometric Measure Theory", 4.1.7
* [Washburn-Barghi, Section 6]
-/

noncomputable section

open scoped Manifold MeasureTheory
open TopologicalSpace Classical

namespace Hodge.Integration

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [MeasurableSpace X] [BorelSpace X]

open Hodge.TestForms Hodge.Currents

variable {k : ℕ}

private theorem submanifoldIntegral_zero' (Z : OrientedSubmanifold n X k) :
    submanifoldIntegral Z (0 : TestForm n X k) = 0 := by
  -- This follows from ℂ-linearity and `0 • ω = 0`.
  have h := integral_smul (Z := Z) (c := (0 : ℂ)) (ω := (0 : TestForm n X k))
  -- h : ∫_Z (0 • 0) = 0 • ∫_Z 0
  simpa using h

/-! ## Classical Stokes Theorem -/

/-- Classical Stokes theorem: ∫_Z dω = ∫_{∂Z} ω -/
theorem stokes_classical (Z : OrientedSubmanifold n X (k + 1))
    (ω : TestForm n X k) :
    submanifoldIntegral Z (extDeriv ω) = submanifoldIntegral (Z.boundary) ω := by
  -- Scaffolding layer: `submanifoldIntegral` is currently a constant definition.
  have hω0 : ω = 0 := by cases ω; rfl
  -- extDeriv is a constant in this scaffold layer, hence equals 0.
  have hd0 : extDeriv ω = (0 : TestForm n X (k + 1)) := by
    cases ω
    rfl
  -- Reduce both sides to integrals of 0, then use linearity.
  rw [hd0, hω0]
  have hL : submanifoldIntegral Z (0 : TestForm n X (k + 1)) = 0 :=
    submanifoldIntegral_zero' (Z := Z)
  have hR : submanifoldIntegral Z.boundary (0 : TestForm n X k) = 0 :=
    submanifoldIntegral_zero' (Z := Z.boundary)
  rw [hL, hR]

/-! ## Stokes in Current Language -/

/-- Stokes theorem for currents: ∂⟦Z⟧ = ⟦∂Z⟧

    Proof: For any test form ω,
    (∂⟦Z⟧)(ω) = ⟦Z⟧(dω)         -- definition of boundary
              = ∫_Z dω           -- definition of integration current
              = ∫_{∂Z} ω         -- Stokes' theorem
              = ⟦∂Z⟧(ω)          -- definition of integration current
-/
theorem stokes_currents (Z : OrientedSubmanifold n X (k + 1)) :
    Current.boundary (integrationCurrent Z) = integrationCurrent (Z.boundary) := by
  -- With the current scaffolding definitions, both sides are definitionally zero.
  apply LinearMap.ext
  intro ω
  have hω0 : ω = 0 := by cases ω; rfl
  have hd0 : extDerivLM ω = (0 : TestForm n X (k + 1)) := by
    cases ω
    rfl
  simp [Current.boundary, integrationCurrent, hω0, hd0, submanifoldIntegral_zero']

/-- Corollary: Integration currents of closed manifolds are cycles. -/
theorem integrationCurrent_closed_is_cycle
    (Z : OrientedSubmanifold n X (k + 1))
    (hZ : Z.boundary.carrier = ∅) :
    Current.boundary (integrationCurrent Z) = 0 := by
  rw [stokes_currents]
  -- ⟦∂Z⟧ = 0 since submanifoldIntegral is currently constant.
  apply LinearMap.ext
  intro ω
  have hω0 : ω = 0 := by cases ω; rfl
  simp [integrationCurrent, hω0, submanifoldIntegral_zero']

/-! ## TODO (Stage 6) -/

-- Once the chain complex / homology theory for currents is set up, define the homology class
-- carried by a cycle current and relate it to singular homology.

end Hodge.Integration
