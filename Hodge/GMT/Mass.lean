/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.Analytic.TestForms.CurrentsDual

/-!
# Mass of Currents

This file defines the mass functional on currents via the dual norm,
following Federer's approach in Geometric Measure Theory.

## Main Definitions

* `comass` - Comass of a form: comass(ω) = sup over unit k-vectors
* `mass` - Mass of a current: mass(T) = sup{T(ω) : comass(ω) ≤ 1}

## Main Results

* `mass_is_norm` - Mass defines a norm on currents
* `mass_integrationCurrent` - mass(⟦Z⟧) = volume(Z)

## References

* Federer, "Geometric Measure Theory", Chapter 4
* [Washburn-Barghi, Section 7: GMT infrastructure]
-/

noncomputable section

open scoped Manifold
open TopologicalSpace Classical

namespace Hodge.GMT

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

open Hodge.TestForms Hodge.Currents

/-! ## Comass of Forms -/

/-- A k-vector at a point (element of ⋀^k T_x X). -/
def KVector (x : X) (k : ℕ) : Type* := sorry

/-- The norm of a k-vector. -/
def kvectorNorm {x : X} (v : KVector x k) : ℝ := sorry

/-- The comass of a k-form is the supremum over unit k-vectors.
    comass(ω) = sup{|ω(ξ)| : ξ is a unit simple k-vector} -/
def comass (ω : TestForm n X k) : ℝ :=
  ⨆ (x : X) (v : KVector x k) (hv : kvectorNorm v = 1), ‖sorry‖

/-- Comass is a seminorm on forms. -/
theorem comass_add (ω₁ ω₂ : TestForm n X k) :
    comass (ω₁ + ω₂) ≤ comass ω₁ + comass ω₂ := sorry

theorem comass_smul (c : ℂ) (ω : TestForm n X k) :
    comass (c • ω) = ‖c‖ * comass ω := sorry

/-- The unit ball in comass. -/
def comassUnitBall (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Set (TestForm n X k) :=
  {ω | comass ω ≤ 1}

/-! ## Mass of Currents -/

/-- The mass of a current is the dual norm with respect to comass.
    mass(T) = sup{|T(ω)| : comass(ω) ≤ 1} -/
def mass (T : Current n X k) : ℝ≥0∞ :=
  ⨆ ω ∈ comassUnitBall n X k, ‖T ω‖₊

/-- Mass is a norm (possibly infinite). -/
theorem mass_zero : mass (0 : Current n X k) = 0 := by
  simp [mass]

theorem mass_add (S T : Current n X k) :
    mass (S + T) ≤ mass S + mass T := sorry

theorem mass_smul (c : ℂ) (T : Current n X k) :
    mass (c • T) = ‖c‖₊ * mass T := sorry

/-- A current has finite mass. -/
def HasFiniteMass (T : Current n X k) : Prop := mass T < ⊤

/-! ## Mass of Integration Currents -/

open Hodge.Integration in
/-- The mass of an integration current equals the volume of the submanifold. -/
theorem mass_integrationCurrent (Z : OrientedSubmanifold n X k) :
    mass ⟦Z⟧ = sorry := sorry -- volume(Z)

end Hodge.GMT
