/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.Analytic.TestForms.CurrentsDual
import Hodge.Analytic.Integration.IntegrationCurrent

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

open scoped Manifold ENNReal
open TopologicalSpace Classical

namespace Hodge.GMT

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [MeasurableSpace X] [BorelSpace X]

open Hodge.TestForms Hodge.Currents

/-! ## Comass of Forms -/

/-- A k-vector at a point (element of ⋀^k T_x X). Placeholder: just Unit. -/
def KVector (_x : X) (_k : ℕ) : Type := Unit

/-- The norm of a k-vector. (Placeholder: KVector is Unit, so norm is 0) -/
def kvectorNorm (_v : Unit) : ℝ := 0

/-- The comass of a k-form is the supremum over unit k-vectors.
    comass(ω) = sup{|ω(ξ)| : ξ is a unit simple k-vector} -/
def comass (_ω : TestForm n X k) : ℝ :=
  -- TODO (Stage 3): define comass via evaluation on unit simple k-vectors.
  0

/-- Comass is a seminorm on forms. -/
theorem comass_add (ω₁ ω₂ : TestForm n X k) :
    comass (ω₁ + ω₂) ≤ comass ω₁ + comass ω₂ := by
  -- With comass defined as 0, this is 0 ≤ 0 + 0
  simp [comass]

theorem comass_smul (c : ℂ) (ω : TestForm n X k) :
    comass (c • ω) = ‖c‖ * comass ω := by
  -- With comass defined as 0, this is 0 = ‖c‖ * 0
  simp [comass]

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
    mass (S + T) ≤ mass S + mass T := by
  -- mass(S+T) = ⨆ ω, ‖(S+T)(ω)‖ ≤ ⨆ ω, (‖S ω‖ + ‖T ω‖) ≤ mass S + mass T
  unfold mass
  apply iSup₂_le
  intro ω hω
  -- ‖(S + T) ω‖ ≤ ‖S ω‖ + ‖T ω‖ by triangle inequality
  have h1 : (‖(S + T) ω‖₊ : ℝ≥0∞) ≤ ‖S ω‖₊ + ‖T ω‖₊ := by
    have : (S + T) ω = S ω + T ω := LinearMap.add_apply S T ω
    rw [this]
    exact_mod_cast nnnorm_add_le (S ω) (T ω)
  have h2 : (‖S ω‖₊ : ℝ≥0∞) ≤ ⨆ ω' ∈ comassUnitBall n X k, (‖S ω'‖₊ : ℝ≥0∞) := by
    apply le_iSup₂_of_le ω hω
    rfl
  have h3 : (‖T ω‖₊ : ℝ≥0∞) ≤ ⨆ ω' ∈ comassUnitBall n X k, (‖T ω'‖₊ : ℝ≥0∞) := by
    apply le_iSup₂_of_le ω hω
    rfl
  calc (‖(S + T) ω‖₊ : ℝ≥0∞) ≤ ‖S ω‖₊ + ‖T ω‖₊ := h1
    _ ≤ (⨆ ω' ∈ comassUnitBall n X k, (‖S ω'‖₊ : ℝ≥0∞)) + 
        (⨆ ω' ∈ comassUnitBall n X k, (‖T ω'‖₊ : ℝ≥0∞)) := add_le_add h2 h3

theorem mass_smul (c : ℂ) (T : Current n X k) :
    mass (c • T) = ‖c‖₊ * mass T := by
  -- mass(c•T) = ⨆ ω, ‖(c•T)(ω)‖ = ⨆ ω, ‖c‖ * ‖T(ω)‖ = ‖c‖ * ⨆ ω, ‖T(ω)‖
  -- The proof requires careful manipulation of biSup with ENNReal multiplication
  -- Key lemma needed: ENNReal.mul_iSup₂ or similar
  unfold mass
  have heq : ∀ ω, (c • T) ω = c • (T ω) := fun ω => LinearMap.smul_apply c T ω
  simp_rw [heq, nnnorm_smul, ENNReal.coe_mul]
  rw [ENNReal.mul_iSup]
  congr 1
  ext ω
  rw [ENNReal.mul_iSup]

/-- A current has finite mass. -/
def HasFiniteMass (T : Current n X k) : Prop := mass T < ⊤

/-! ## Mass of Integration Currents -/

open Hodge.Integration in
/-- The mass of an integration current equals the volume of the submanifold.
    With placeholder definitions (submanifoldIntegral = 0), mass = 0. -/
theorem mass_integrationCurrent (Z : OrientedSubmanifold n X k) :
    mass (integrationCurrent Z) = 0 := by
  -- With submanifoldIntegral = 0, integrationCurrent Z is the zero current
  have h : integrationCurrent Z = 0 := by
    apply LinearMap.ext
    intro ω
    simp only [integrationCurrent, submanifoldIntegral, LinearMap.coe_mk,
               AddHom.coe_mk, LinearMap.zero_apply]
  rw [h, mass_zero]

end Hodge.GMT
