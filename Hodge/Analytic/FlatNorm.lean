import Hodge.Analytic.Currents
import Hodge.Analytic.Norms
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Track B.5: Flat Norm

This file defines the flat norm on currents and proves its basic properties.
The flat norm is the natural metric for the space of integral currents.

## Mathlib Integration

We leverage Mathlib's infimum/supremum machinery:
- `Real.sInf_nonneg`: Infimum of non-negative set is non-negative
- `csInf_le`: Infimum is a lower bound
- `le_csInf`: Infimum is the greatest lower bound

## Contents
- Flat norm definition
- Triangle inequality
- Relationship with mass norm
- Interface with compactness theorems
-/

noncomputable section

open Classical Set

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- The flat norm of a current T.
Defined as the infimum of mass(T - ∂Q) + mass(Q) over all (k+1)-currents Q.

This uses Mathlib's `sInf` (infimum over a set of reals). -/
def flatNorm {k : ℕ} (T : Current n X k) : ℝ :=
  sInf { r : ℝ | ∃ (Q : Current n X (k + 1)), r = (T - Q.boundary).mass + Q.mass }

/-- The flat norm is non-negative.

Proof uses `Real.sInf_nonneg`: the infimum of a set of non-negative numbers is non-negative. -/
theorem flatNorm_nonneg {k : ℕ} (T : Current n X k) :
    flatNorm T ≥ 0 := by
  unfold flatNorm
  apply Real.sInf_nonneg
  rintro r ⟨Q, h_val⟩
  rw [h_val]
  apply add_nonneg
  · apply Current.mass_nonneg
  · apply Current.mass_nonneg

/-- The flat norm is bounded above by the mass.

Proof: Choose Q = 0, then flat norm ≤ mass(T - 0) + mass(0) = mass(T).
Uses `csInf_le` to show infimum is at most any element of the set. -/
theorem flatNorm_le_mass {k : ℕ} (T : Current n X k) :
    flatNorm T ≤ T.mass := by
  unfold flatNorm
  -- Choose Q = 0
  apply csInf_le
  · -- The set is bounded below by 0
    use 0
    intro r ⟨Q, hr⟩
    rw [hr]
    apply add_nonneg <;> apply Current.mass_nonneg
  · -- mass(T) is in the set (with Q = 0)
    use 0
    -- (0 : Current).boundary = 0, and T - 0 = T, mass(0) = 0
    have h1 : (0 : Current n X (k + 1)).boundary = 0 := by
      apply LinearMap.ext; intro ω
      simp only [Current.boundary, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
    simp only [h1, sub_zero, Current.mass_zero, add_zero]

/-- The flat norm satisfies the triangle inequality.

Proof outline: Given decompositions S = (S - ∂Q₁) + ∂Q₁ and T = (T - ∂Q₂) + ∂Q₂,
we have S + T = ((S + T) - ∂(Q₁ + Q₂)) + ∂(Q₁ + Q₂). -/
theorem flatNorm_add_le {k : ℕ} (S T : Current n X k) :
    flatNorm (S + T) ≤ flatNorm S + flatNorm T := by
  -- For any ε > 0, find Q₁, Q₂ achieving near-optimal decompositions
  -- Then Q₁ + Q₂ gives a decomposition for S + T
  sorry

/-- Fundamental estimate: |T(ψ)| ≤ flatNorm(T) * C where C depends on comass of ψ and dψ.

This shows that flat norm convergence implies weak-* convergence.
Proof: T(ψ) = (T - ∂Q)(ψ) + (∂Q)(ψ) = (T - ∂Q)(ψ) + Q(dψ)
       |T(ψ)| ≤ mass(T - ∂Q)·comass(ψ) + mass(Q)·comass(dψ) -/
theorem eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T ψ| ≤ flatNorm T * max (comass ψ) (comass (smoothExtDeriv ψ)) := by
  sorry

end
