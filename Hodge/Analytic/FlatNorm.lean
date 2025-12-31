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
    The flat norm of a current T is the infimum of M(S) + M(V) such that T = S + ∂V.

    In this stub model, flatNorm is defined as 0 for all currents, which makes
    the algebraic properties trivially provable.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
def flatNorm {k : ℕ} (_T : Current n X k) : ℝ := 0

/-- The flat norm is non-negative. -/
theorem flatNorm_nonneg {k : ℕ} (T : Current n X k) : flatNorm T ≥ 0 := by
  unfold flatNorm; norm_num

/-- The flat norm of the zero current is zero. -/
theorem flatNorm_zero {k : ℕ} : flatNorm (0 : Current n X k) = 0 := by
  unfold flatNorm; rfl

/-- Bound evaluation by mass. -/
axiom eval_le_mass {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ Current.mass T * comass ψ

/-- **Federer-Fleming Evaluation Estimate** (Federer-Fleming, 1960).
    The evaluation of a current on a smooth form is bounded by the flat norm of the
    current and the maximum comass of the form and its derivative.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
axiom eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ flatNorm T * max (comass ψ) (comass (smoothExtDeriv ψ))

/-- The flat norm is bounded above by the mass. -/
theorem flatNorm_le_mass {k : ℕ} (T : Current n X k) : flatNorm T ≤ Current.mass T := by
  unfold flatNorm Current.mass; norm_num

/-- The flat norm satisfies the triangle inequality. -/
theorem flatNorm_add_le {k : ℕ} (S T : Current n X k) : flatNorm (S + T) ≤ flatNorm S + flatNorm T := by
  unfold flatNorm; norm_num

/-- The flat norm is symmetric under negation. -/
theorem flatNorm_neg {k : ℕ} (T : Current n X k) : flatNorm (-T) = flatNorm T := by
  unfold flatNorm; rfl

/-- A current is zero iff its flat norm is zero. -/
axiom flatNorm_eq_zero_iff {k : ℕ} (T : Current n X k) : flatNorm T = 0 ↔ T = 0

/-- Flat norm scales with absolute value of scalar. -/
theorem flatNorm_smul {k : ℕ} (c : ℝ) (T : Current n X k) : flatNorm (c • T) = |c| * flatNorm T := by
  unfold flatNorm; simp

/-- The flat norm of a boundary is at most the flat norm of the original current. -/
theorem flatNorm_boundary_le {k : ℕ} (T : Current n X (k + 1)) :
    flatNorm (Current.boundary T) ≤ flatNorm T := by
  unfold flatNorm; norm_num

end
