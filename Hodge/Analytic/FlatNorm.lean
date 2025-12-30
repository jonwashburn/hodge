import Hodge.Analytic.Currents
import Hodge.Analytic.Norms
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Filter.Basic

/-!
# Track B.5: Flat Norm
-/

noncomputable section

open Classical Set Filter Topology

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

/-- The flat norm of the zero current is zero. -/
axiom flatNorm_zero {k : ℕ} : flatNorm (0 : Current n X k) = 0

/-- The flat norm is zero iff the current is zero. -/
axiom flatNorm_eq_zero_iff {k : ℕ} (T : Current n X k) : flatNorm T = 0 ↔ T = 0

/-- The flat norm is symmetric. -/
axiom flatNorm_neg {k : ℕ} (T : Current n X k) : flatNorm (-T) = flatNorm T

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

/-- **Continuity of Evaluation in Flat Norm**
    The evaluation of a current on a smooth form is continuous with respect to
    the flat norm topology. -/
theorem tendsto_eval_of_flat_conv {k : ℕ} {T : ℕ → Current n X k} {T_limit : Current n X k}
    (ψ : SmoothForm n X k)
    (h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    Tendsto (fun i => (T i).toFun ψ) atTop (nhds (T_limit.toFun ψ)) := by
  let C := max (comass ψ) (comass (smoothExtDeriv ψ))
  have h_bound : ∀ i, |(T i).toFun ψ - T_limit.toFun ψ| ≤ flatNorm (T i - T_limit) * C := by
    intro i
    -- Evaluation difference is evaluation of the difference current
    have : (T i).toFun ψ - T_limit.toFun ψ = (T i - T_limit).toFun ψ := rfl
    rw [this]
    -- Apply the Federer-Fleming evaluation estimate
    exact eval_le_flatNorm _ _
  
  -- Use the sandwich theorem (tendsto_of_tendsto_of_tendsto_of_le_of_le)
  -- |f(i) - L| ≤ g(i) and g(i) → 0 implies f(i) → L
  -- This is equivalent to L - g(i) ≤ f(i) ≤ L + g(i)
  have h_low : ∀ i, T_limit.toFun ψ - flatNorm (T i - T_limit) * C ≤ (T i).toFun ψ := by
    intro i; have h := h_bound i; rw [abs_le] at h; linarith
  have h_high : ∀ i, (T i).toFun ψ ≤ T_limit.toFun ψ + flatNorm (T i - T_limit) * C := by
    intro i; have h := h_bound i; rw [abs_le] at h; linarith
    
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (f := fun i => (T i).toFun ψ)
    (g := fun i => T_limit.toFun ψ - flatNorm (T i - T_limit) * C)
    (h := fun i => T_limit.toFun ψ + flatNorm (T i - T_limit) * C)
  · -- Lower bound converges to T_limit(ψ)
    have h_lim := h_conv.mul_const C
    simp only [mul_zero] at h_lim
    have h_sub := Tendsto.sub (tendsto_const_nhds (x := T_limit.toFun ψ)) h_lim
    simpa using h_sub
  · -- Upper bound converges to T_limit(ψ)
    have h_lim := h_conv.mul_const C
    simp only [mul_zero] at h_lim
    have h_add := Tendsto.add (tendsto_const_nhds (x := T_limit.toFun ψ)) h_lim
    simpa using h_add
  · exact h_low
  · exact h_high

/-- **Boundary estimate in Flat Norm**
    The flat norm of the boundary is bounded by the flat norm of the current.
    Reference: [H. Federer, "Geometric Measure Theory", 1969]. -/
axiom flatNorm_boundary_le {k : ℕ} (T : Current n X (k + 1)) :
    flatNorm (T.boundary) ≤ flatNorm T

/-- **Continuity of Boundary in Flat Norm**
    The boundary operator is continuous with respect to the flat norm topology. -/
theorem tendsto_boundary_of_flat_conv {k : ℕ} {T : ℕ → Current n X (k + 1)} {T_limit : Current n X (k + 1)}
    (h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    Tendsto (fun i => flatNorm ((T i).boundary - T_limit.boundary)) atTop (nhds 0) := by
  -- Boundary operator is linear
  have h_linear : ∀ i, (T i).boundary - T_limit.boundary = (T i - T_limit).boundary := by
    intro i; ext ω; rfl
  simp_rw [h_linear]
  -- Squeeze theorem between 0 and flatNorm (T i - T_limit)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (f := fun i => flatNorm (T i - T_limit).boundary)
    (g := fun _ => 0) (h := fun i => flatNorm (T i - T_limit))
  · exact tendsto_const_nhds
  · exact h_conv
  · exact fun i => flatNorm_nonneg _
  · exact fun i => flatNorm_boundary_le _

end
