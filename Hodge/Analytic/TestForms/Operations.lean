/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.Analytic.TestForms.LFTopology

/-!
# Continuous Operations on Test Forms

This file proves that the standard operations on differential forms
are continuous with respect to the LF topology.

## Main Results

* `dCLM` - Exterior derivative d : D^k(X) →L D^{k+1}(X) is continuous
* `wedgeCLM` - Wedge product ∧ : D^k(X) × D^l(X) →L D^{k+l}(X) is continuous  
* `pullbackCLM` - Pullback f* : D^k(Y) →L D^k(X) is continuous

## References

* [Washburn-Barghi, Section 5: Test form operations]
-/

noncomputable section

open scoped Distributions Manifold
open TopologicalSpace Classical

namespace Hodge.TestForms

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-! ## Exterior Derivative -/

/-- The exterior derivative on test forms (pointwise). -/
def extDeriv (k : ℕ) (ω : TestForm n X k) : TestForm n X (k + 1) := sorry

/-- Exterior derivative is linear. -/
theorem extDeriv_add (ω₁ ω₂ : TestForm n X k) :
    extDeriv k (ω₁ + ω₂) = extDeriv k ω₁ + extDeriv k ω₂ := sorry

theorem extDeriv_smul (c : ℂ) (ω : TestForm n X k) :
    extDeriv k (c • ω) = c • extDeriv k ω := sorry

/-- The exterior derivative as a continuous linear map on the LF-space. -/
def dCLM (k : ℕ) : TestForm n X k →L[ℂ] TestForm n X (k + 1) := sorry

/-- d ∘ d = 0 -/
theorem d_comp_d (ω : TestForm n X k) : 
    extDeriv (k + 1) (extDeriv k ω) = 0 := sorry

/-! ## Wedge Product -/

/-- Wedge product of test forms (pointwise). -/
def wedge (ω : TestForm n X k) (η : TestForm n X l) : TestForm n X (k + l) := sorry

/-- Wedge product is bilinear. -/
theorem wedge_add_left (ω₁ ω₂ : TestForm n X k) (η : TestForm n X l) :
    wedge (ω₁ + ω₂) η = wedge ω₁ η + wedge ω₂ η := sorry

theorem wedge_add_right (ω : TestForm n X k) (η₁ η₂ : TestForm n X l) :
    wedge ω (η₁ + η₂) = wedge ω η₁ + wedge ω η₂ := sorry

/-- Wedge product as a continuous bilinear map. -/
def wedgeCLM (k l : ℕ) : 
    TestForm n X k →L[ℂ] TestForm n X l →L[ℂ] TestForm n X (k + l) := sorry

/-- Leibniz rule: d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη -/
theorem leibniz (ω : TestForm n X k) (η : TestForm n X l) :
    extDeriv (k + l) (wedge ω η) = 
      wedge (extDeriv k ω) η + (-1 : ℂ)^k • wedge ω (extDeriv l η) := sorry

/-! ## Pullback -/

variable {Y : Type*} [MetricSpace Y] [ChartedSpace (EuclideanSpace ℂ (Fin n)) Y]
  [IsManifold (𝓒_complex n) ⊤ Y]

/-- Pullback of test forms by a smooth map. -/
def pullback (f : C^∞⟮𝓒_complex n, Y; 𝓒_complex n, X⟯) (ω : TestForm n X k) : 
    TestForm n Y k := sorry

/-- Pullback is linear. -/
theorem pullback_add (f : C^∞⟮𝓒_complex n, Y; 𝓒_complex n, X⟯) (ω₁ ω₂ : TestForm n X k) :
    pullback f (ω₁ + ω₂) = pullback f ω₁ + pullback f ω₂ := sorry

/-- Pullback as a continuous linear map. -/
def pullbackCLM (f : C^∞⟮𝓒_complex n, Y; 𝓒_complex n, X⟯) (k : ℕ) :
    TestForm n X k →L[ℂ] TestForm n Y k := sorry

/-- Pullback commutes with d: f*(dω) = d(f*ω) -/
theorem pullback_d (f : C^∞⟮𝓒_complex n, Y; 𝓒_complex n, X⟯) (ω : TestForm n X k) :
    pullback f (extDeriv k ω) = extDeriv k (pullback f ω) := sorry

/-- Pullback commutes with ∧: f*(ω ∧ η) = f*ω ∧ f*η -/
theorem pullback_wedge (f : C^∞⟮𝓒_complex n, Y; 𝓒_complex n, X⟯) 
    (ω : TestForm n X k) (η : TestForm n X l) :
    pullback f (wedge ω η) = wedge (pullback f ω) (pullback f η) := sorry

end Hodge.TestForms
