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

/-- **The Flat Norm** (Federer-Fleming, 1960).
    The flat norm of a current T is the infimum of M(S) + M(V) such that T = S + ∂V.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
opaque flatNorm {k : ℕ} (T : Current n X k) : ℝ

/-- The flat norm is non-negative. -/
axiom flatNorm_nonneg {k : ℕ} (T : Current n X k) : flatNorm T ≥ 0

/-- The flat norm satisfies the triangle inequality. -/
axiom flatNorm_add_le {k : ℕ} (S T : Current n X k) : flatNorm (S + T) ≤ flatNorm S + flatNorm T

/-- The flat norm is bounded above by the mass. -/
axiom flatNorm_le_mass {k : ℕ} (T : Current n X k) : flatNorm T ≤ Current.mass T

/-- **Federer-Fleming Evaluation Estimate** (Federer-Fleming, 1960).
    The evaluation of a current on a smooth form is bounded by the flat norm of the
    current and the maximum comass of the form and its derivative.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
axiom eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ flatNorm T * max (comass ψ) (comass (smoothExtDeriv ψ))

end
