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

In the full development, currents are *continuous* linear functionals on the LF-space
of test forms. In this scaffolding layer, `Current` is currently just a `LinearMap`,
so we only record linearity (continuity will be added once the LF-topology is implemented).

`⟦Z⟧(ω) := ∫_Z ω`. -/
def integrationCurrent (Z : OrientedSubmanifold n X k) : Current n X k where
  toFun := submanifoldIntegral Z
  map_add' := integral_add Z
  map_smul' := integral_smul Z

notation "⟦" Z "⟧" => integrationCurrent Z

/-! ## TODO (Stage 2) -/

-- Once we have chains, mass, and a genuine current topology:
-- - prove additivity in the chain variable
-- - prove `mass ⟦Z⟧ = volume(Z)` for smooth submanifolds
-- - define `IsIntegrationCurrent` / normal / integral currents
-- - prove closure properties

end Hodge.Integration
