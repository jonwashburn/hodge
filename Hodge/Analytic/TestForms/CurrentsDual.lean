/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.Analytic.TestForms.Operations

/-!
# Currents as Continuous Linear Functionals

Currents are the dual space of test forms.

## Main Definitions

* `Current` - k-currents as (D^k(X))'
* `Current.boundary` - Boundary operator ∂T(ω) = T(dω)

## Main Results

* `boundary_boundary` - ∂∂ = 0

## References

* de Rham, "Differentiable Manifolds"
* [Washburn-Barghi, Section 6]
-/

noncomputable section

open scoped Distributions
open TopologicalSpace Classical

namespace Hodge.Currents

variable {n : ℕ} {X : Type*} {k : ℕ}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

open Hodge.TestForms

/-! ## Current Definition -/

/-- A k-current on X is a continuous linear functional on test k-forms. -/
def Current (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :=
  TestForm n X k →ₗ[ℂ] ℂ

namespace Current

instance : CoeFun (Current n X k) (fun _ => TestForm n X k → ℂ) :=
  ⟨fun T => T.toFun⟩

instance : AddCommGroup (Current n X k) := LinearMap.addCommGroup

instance : Module ℂ (Current n X k) := LinearMap.module

/-! ## Boundary Operator -/

/-- The boundary of a (k+1)-current T is the k-current defined by ∂T(ω) = T(dω). -/
def boundary (T : Current n X (k + 1)) : Current n X k :=
  T.comp extDerivLM

/-- ∂∂ = 0 -/
theorem boundary_boundary (T : Current n X (k + 2)) :
    boundary (boundary T) = 0 := by
  apply LinearMap.ext
  intro ω
  simp only [boundary, LinearMap.comp_apply, LinearMap.zero_apply]
  have h : extDeriv (extDeriv ω) = 0 := d_comp_d ω
  simp [extDerivLM, h]

end Current

end Hodge.Currents
