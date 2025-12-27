import Hodge.Analytic.Currents
import Hodge.Analytic.Norms

/-!
# Track B.5: Flat Norm

This file defines the flat norm on currents and proves its basic properties.
The flat norm is the natural metric for the space of integral currents.

## Contents
- Flat norm definition
- Triangle inequality
- Relationship with mass norm
- Interface with compactness theorems
-/

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- The flat norm of a current T.
Defined as the infimum of mass(T - ∂Q) + mass(Q) over all (k+1)-currents Q. -/
def flatNorm {k : ℕ} (T : Current n X k) : ℝ :=
  sInf { r : ℝ | ∃ (Q : Current n X (k + 1)), r = (T - Q.boundary).mass + Q.mass }

/-- The flat norm is non-negative. -/
theorem flatNorm_nonneg {k : ℕ} (T : Current n X k) :
    flatNorm T ≥ 0 := by
  unfold flatNorm
  apply Real.sInf_nonneg
  rintro r ⟨Q, h_val⟩
  rw [h_val]
  apply add_nonneg
  · apply Current.mass_nonneg
  · apply Current.mass_nonneg

/-- The flat norm is bounded above by the mass. (Choose Q = 0) -/
theorem flatNorm_le_mass {k : ℕ} (T : Current n X k) :
    flatNorm T ≤ T.mass := by
  sorry

/-- The flat norm satisfies the triangle inequality. -/
theorem flatNorm_add_le {k : ℕ} (S T : Current n X k) :
    flatNorm (S + T) ≤ flatNorm S + flatNorm T := by
  sorry

/-- Fundamental estimate: |T(ψ)| ≤ flatNorm(T) * C where C depends on comass of ψ and dψ.
This shows that flat norm convergence implies weak-* convergence. -/
theorem eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T ψ| ≤ flatNorm T * max (comass ψ) (comass (smoothExtDeriv ψ)) := by
  sorry

end
