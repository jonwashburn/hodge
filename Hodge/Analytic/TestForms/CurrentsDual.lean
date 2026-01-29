/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.Analytic.TestForms.Operations

/-!
# Currents as Continuous Linear Functionals

This file defines currents as continuous linear functionals on the LF-space
of test forms, following the distributional approach.

## Main Definitions

* `Current` - k-currents as (D^k(X))'
* `Current.boundary` - Boundary operator ∂T(ω) = T(dω)

## Main Results

* `boundary_boundary` - ∂∂ = 0
* `Current.chainComplex` - Currents form a chain complex

## References

* de Rham, "Differentiable Manifolds"
* Federer, "Geometric Measure Theory"
* [Washburn-Barghi, Section 6]
-/

noncomputable section

open scoped Distributions Manifold
open TopologicalSpace Classical

namespace Hodge.Currents

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

open Hodge.TestForms

/-! ## Current Definition -/

/-- A k-current on X is a continuous linear functional on test k-forms.
    This is the distributional definition from GMT. -/
def Current (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :=
  TestForm n X k →L[ℂ] ℂ

namespace Current

variable {k : ℕ}

instance : CoeFun (Current n X k) (fun _ => TestForm n X k → ℂ) :=
  ContinuousLinearMap.toCoeFun

instance : AddCommGroup (Current n X k) := ContinuousLinearMap.addCommGroup

instance : Module ℂ (Current n X k) := ContinuousLinearMap.module

/-! ## Boundary Operator -/

/-- The boundary of a (k+1)-current T is the k-current defined by ∂T(ω) = T(dω). -/
def boundary (T : Current n X (k + 1)) : Current n X k :=
  T.comp (dCLM k)

/-- Boundary is linear. -/
theorem boundary_add (S T : Current n X (k + 1)) :
    boundary (S + T) = boundary S + boundary T := by
  ext ω
  simp [boundary]

theorem boundary_smul (c : ℂ) (T : Current n X (k + 1)) :
    boundary (c • T) = c • boundary T := by
  ext ω
  simp [boundary]

/-- ∂∂ = 0 (boundary of boundary is zero) -/
theorem boundary_boundary (T : Current n X (k + 2)) :
    boundary (boundary T) = 0 := by
  ext ω
  simp only [boundary, ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  -- Need: T(d(dω)) = 0, which follows from d∘d = 0
  have h : extDeriv (k + 1) (extDeriv k ω) = 0 := d_comp_d ω
  simp [h]

/-! ## Chain Complex Structure -/

/-- The boundary operator as a linear map. -/
def boundaryLM : Current n X (k + 1) →ₗ[ℂ] Current n X k where
  toFun := boundary
  map_add' := boundary_add
  map_smul' := boundary_smul

/-- Currents form a chain complex: im(∂_{k+1}) ⊆ ker(∂_k) -/
theorem chainComplex : ∀ T : Current n X (k + 2), 
    boundaryLM (boundaryLM T) = 0 := 
  boundary_boundary

/-! ## Support of a Current -/

/-- The support of a current (to be defined properly). -/
def support (T : Current n X k) : Set X := sorry

/-- Currents with compact support. -/
def HasCompactSupport (T : Current n X k) : Prop := IsCompact (support T)

end Current

end Hodge.Currents
