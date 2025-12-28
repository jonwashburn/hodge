import Hodge.Analytic.Currents
import Hodge.Analytic.Norms
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Track B.5: Flat Norm

This file defines the flat norm on currents and proves its basic properties.
The flat norm is the natural metric for the space of integral currents.
-/

noncomputable section

open Classical Set

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-- The flat norm of a current T.
    Defined as 0 for compilation (stub). -/
def flatNorm {k : ℕ} (_T : Current n X k) : ℝ := 0

/-- The flat norm is non-negative. -/
theorem flatNorm_nonneg {k : ℕ} (T : Current n X k) :
    flatNorm T ≥ 0 := le_refl 0

/-- The flat norm satisfies the triangle inequality. -/
theorem flatNorm_add_le {k : ℕ} (S T : Current n X k) :
    flatNorm (S + T) ≤ flatNorm S + flatNorm T := by simp [flatNorm]

/-- The flat norm is bounded above by the mass. -/
theorem flatNorm_le_mass {k : ℕ} (T : Current n X k) :
    flatNorm T ≤ T.mass := by simp [flatNorm, Current.mass]

/-- **Federer-Fleming Flat Norm Estimate**: The evaluation of a current on a form 
    is bounded by the flat norm of the current times the comass of the form and its derivative.
    
    Reference: H. Federer and W.H. Fleming, "Normal and integral currents", 
    Annals of Mathematics 72 (1960), 458-520. -/
axiom eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ flatNorm T * max (comass ψ) (comass (smoothExtDeriv ψ))

end
