import Hodge.Analytic.Currents
import Hodge.Analytic.Norms
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!

This file defines the flat norm on currents and proves its basic properties.
The flat norm is the natural metric for the space of integral currents.

Since `Current` operations are opaque, most properties are axiomatized.
-/

noncomputable section

open Classical Set

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-- **The Flat Norm** (Federer-Fleming, 1960).
    The flat norm of a current T is the infimum of M(S) + M(V) such that T = S + ∂V:
    F(T) = inf { M(S) + M(V) : T = S + ∂V }

    This requires the full GMT machinery and is defined opaquely.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
opaque flatNorm {k : ℕ} (T : Current n X k) : ℝ

/-- The flat norm is non-negative (Federer-Fleming 1960). -/
axiom flatNorm_nonneg {k : ℕ} (T : Current n X k) : flatNorm T ≥ 0

/-- The flat norm of the zero current is zero. -/
axiom flatNorm_zero {k : ℕ} : flatNorm (0 : Current n X k) = 0

/-- Bound evaluation by mass. -/
axiom eval_le_mass {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ Current.mass T * comass ψ

/-- **Federer-Fleming Evaluation Estimate** (Federer-Fleming, 1960).
    The evaluation of a current on a smooth form is bounded by the flat norm of the
    current and the maximum comass of the form and its derivative.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
axiom eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ flatNorm T * max (comass ψ) (comass (smoothExtDeriv ψ))

/-- The flat norm is bounded above by the mass (Federer-Fleming 1960).
    This follows since T = T + ∂0 with M(T) + M(0) = M(T). -/
axiom flatNorm_le_mass {k : ℕ} (T : Current n X k) : flatNorm T ≤ Current.mass T

/-- The flat norm satisfies the triangle inequality (Federer-Fleming 1960). -/
axiom flatNorm_add_le {k : ℕ} (S T : Current n X k) : flatNorm (S + T) ≤ flatNorm S + flatNorm T

/-- The flat norm is symmetric under negation. -/
axiom flatNorm_neg {k : ℕ} (T : Current n X k) : flatNorm (-T) = flatNorm T

/-- A current is zero iff its flat norm is zero. -/
axiom flatNorm_eq_zero_iff {k : ℕ} (T : Current n X k) : flatNorm T = 0 ↔ T = 0

/-- Flat norm scales with absolute value of scalar. -/
axiom flatNorm_smul {k : ℕ} (c : ℝ) (T : Current n X k) : flatNorm (c • T) = |c| * flatNorm T

/-- The flat norm of a boundary is at most the flat norm of the original current.
    This follows since ∂T = 0 + ∂T with M(0) + M(T) = M(T) ≥ F(T). -/
axiom flatNorm_boundary_le {k : ℕ} (T : Current n X (k + 1)) :
    flatNorm (Current.boundary T) ≤ flatNorm T

end
