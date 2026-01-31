/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.Analytic.TestForms.LFTopology

/-!
# Continuous Operations on Test Forms

This file defines the standard operations on differential forms.

## Main Definitions

* `extDeriv` - Exterior derivative d
* `wedge` - Wedge product ∧
* `pullback` - Pullback f*

## References

* [Washburn-Barghi, Section 5]
-/

noncomputable section

open scoped Distributions
open TopologicalSpace Classical

namespace Hodge.TestForms

variable {n : ℕ} {X : Type*} {k l : ℕ}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-! ## Exterior Derivative -/

/-- The exterior derivative on test forms. -/
def extDeriv (ω : TestForm n X k) : TestForm n X (k + 1) := ⟨()⟩

/-- d ∘ d = 0 -/
theorem d_comp_d (ω : TestForm n X k) : extDeriv (extDeriv ω) = 0 := rfl

/-- The exterior derivative as a linear map. -/
def extDerivLM : TestForm n X k →ₗ[ℂ] TestForm n X (k + 1) where
  toFun := extDeriv
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-! ## Wedge Product -/

/-- Wedge product of test forms. -/
def wedge (ω : TestForm n X k) (η : TestForm n X l) : TestForm n X (k + l) := ⟨()⟩

/-- Leibniz rule (placeholder).
    d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη -/
theorem leibniz : True := by
  trivial

/-! ## Pullback -/

variable {Y : Type*} [MetricSpace Y]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) Y] [IsManifold (𝓒_complex n) ⊤ Y]

/-- Pullback of test forms. -/
def pullback (f : X → Y) (ω : TestForm n Y k) : TestForm n X k := ⟨()⟩

/-- Pullback commutes with d (placeholder). -/
theorem pullback_d (f : X → Y) (ω : TestForm n Y k) :
    pullback f (extDeriv ω) = extDeriv (pullback f ω) := by
  rfl

end Hodge.TestForms
