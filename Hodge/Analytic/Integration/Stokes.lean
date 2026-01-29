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

/-! ## Classical Stokes Theorem -/

/-- Classical Stokes theorem: ∫_Z dω = ∫_{∂Z} ω -/
theorem stokes_classical (Z : OrientedSubmanifold n X (k + 1)) 
    (ω : TestForm n X k) :
    ∫_Z, extDeriv k ω = ∫_(Z.boundary), ω := sorry

/-! ## Stokes in Current Language -/

/-- Stokes theorem for currents: ∂⟦Z⟧ = ⟦∂Z⟧
    
    Proof: For any test form ω,
    (∂⟦Z⟧)(ω) = ⟦Z⟧(dω)         -- definition of boundary
              = ∫_Z dω           -- definition of integration current
              = ∫_{∂Z} ω         -- Stokes' theorem
              = ⟦∂Z⟧(ω)          -- definition of integration current
-/
theorem stokes_currents (Z : OrientedSubmanifold n X (k + 1)) :
    Current.boundary ⟦Z⟧ = ⟦Z.boundary⟧ := by
  ext ω
  simp only [Current.boundary, integrationCurrent, ContinuousLinearMap.comp_apply,
             ContinuousLinearMap.coe_mk']
  exact stokes_classical Z ω

/-- Corollary: Integration currents of closed manifolds are cycles. -/
theorem integrationCurrent_closed_is_cycle 
    (Z : OrientedSubmanifold n X (k + 1))
    (hZ : Z.boundary.carrier = ∅) :
    Current.boundary ⟦Z⟧ = 0 := by
  rw [stokes_currents]
  -- ⟦∂Z⟧ = 0 when ∂Z is empty
  sorry

/-! ## Relation to Homology -/

/-- Integration currents of cycles represent homology classes. -/
def homologyClass (Z : OrientedSubmanifold n X k) 
    (hZ : Current.boundary ⟦Z⟧ = 0) : sorry := sorry

end Hodge.Integration
