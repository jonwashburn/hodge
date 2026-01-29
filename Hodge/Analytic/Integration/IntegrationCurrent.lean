/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.Analytic.Integration.SubmanifoldIntegral
import Hodge.Analytic.TestForms.CurrentsDual

/-!
# Integration Currents

This file defines the integration current [Z] associated to an oriented
submanifold Z, defined by [Z](ω) = ∫_Z ι*ω.

## Main Definitions

* `integrationCurrent` - The current [Z] for a submanifold Z

## Main Results

* `integrationCurrent_continuous` - [Z] is continuous on test forms
* `integrationCurrent_linear` - [Z] is linear

## References

* de Rham, "Differentiable Manifolds"
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

/-! ## Integration Current -/

/-- The integration current associated to an oriented submanifold.
    [Z](ω) := ∫_Z ι*ω where ι : Z ↪ X is the inclusion. -/
def integrationCurrent (Z : OrientedSubmanifold n X k) : Current n X k where
  toFun := submanifoldIntegral Z
  map_add' := integral_add Z
  map_smul' := fun c ω => by
    simp only [integral_smul, RingHom.id_apply]
  cont := integral_continuous Z

notation "⟦" Z "⟧" => integrationCurrent Z

/-- Integration current is linear in the submanifold (for chains). -/
theorem integrationCurrent_add_chain 
    (Z₁ Z₂ : OrientedSubmanifold n X k) (ω : TestForm n X k) :
    sorry := sorry -- Need chain structure

/-- The mass of an integration current equals the volume. -/
theorem integrationCurrent_mass (Z : OrientedSubmanifold n X k) :
    sorry := sorry -- mass(⟦Z⟧) = volume(Z)

/-! ## Relation to Currents Module -/

/-- Integration currents are the "nice" currents. -/
def IsIntegrationCurrent (T : Current n X k) : Prop :=
  ∃ Z : OrientedSubmanifold n X k, T = ⟦Z⟧

/-- Integration currents are closed under addition. -/
theorem integrationCurrent_add_closed : sorry := sorry

end Hodge.Integration
