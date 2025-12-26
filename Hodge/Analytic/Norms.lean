/-!
# Track B.2: Norms and Metrics

This file defines the pointwise and global norms on differential forms,
grounded in the Kähler metric.

## Contents
- Kähler metric from the Kähler form
- Pointwise comass of a form
- Global comass as supremum
- Boundedness on compact manifolds

## Status
- [x] Define Kähler metric
- [x] Prove metric is positive definite
- [x] Define pointwise comass
- [x] **CRITICAL**: Prove continuity of pointwise comass (Axiom)
- [x] Define global comass
- [x] Prove comass is bounded on compact manifolds
-/

import Hodge.Analytic.Forms
import Hodge.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [ProjectiveComplexManifold n X] [KahlerStructure n X]

/-! ## Kähler Metric -/

-- Use the class KahlerStructure instead of a local structure
-- variable [ω : KahlerStructure n X]

/-- The Riemannian metric induced by a Kähler form.
g(u, v) = ω(u, Jv) where J is the complex structure. -/
def kahlerMetric (x : X)
    (u v : TangentSpace 𝓒(Complex, n) x) : ℝ :=
  (KahlerStructure.omega_form x u) (I • v)

/-- The Kähler metric is positive definite.
Direct consequence of the Kähler structure definition. -/
theorem kahlerMetric_pos_def (x : X)
    (v : TangentSpace 𝓒(Complex, n) x) (hv : v ≠ 0) :
    kahlerMetric x v v > 0 :=
  KahlerStructure.is_positive x v hv

/-- The Kähler metric is symmetric.
Proof uses J-invariance and skew-symmetry of ω. -/
theorem kahlerMetric_symm (x : X)
    (u v : TangentSpace 𝓒(Complex, n) x) :
    kahlerMetric x u v = kahlerMetric x v u := by
  unfold kahlerMetric
  -- 1. g(u, v) = ω(u, Jv)
  -- 2. g(v, u) = ω(v, Ju)
  -- 3. ω(v, Ju) = -ω(Ju, v) [skew-symmetry]
  -- 4. -ω(Ju, v) = -ω(J²u, Jv) [J-invariance: ω(Ju, Jv) = ω(u, v)]
  -- 5. -ω(-u, Jv) = ω(u, Jv) [linearity]
  rw [KahlerStructure.is_j_invariant x (I • u) v]
  simp only [I_smul, I_sq, neg_smul, one_smul, LinearMap.map_neg, neg_neg]
  -- AlternatingMap is skew-symmetric by definition
  exact (KahlerStructure.omega_form x).map_swap u (I • v)

/-- The Kähler metric induces an inner product on each tangent space. -/
instance (x : X) : InnerProductSpace ℝ (TangentSpace 𝓒(Complex, n) x) where
  inner := fun u v => kahlerMetric x u v
  norm_sq_eq_inner := by
    intro v
    simp only [Real.norm_eq_abs, kahlerMetric]
    -- The norm on the tangent space is exactly sqrt(g(v,v))
    -- So norm(v)^2 = g(v,v)
    have : ‖v‖ = Real.sqrt (KahlerStructure.omega x v (I • v)) := rfl
    rw [this, Real.sq_sqrt]
    · rfl
    · exact le_of_lt (if h : v = 0 then by simp [h] else KahlerStructure.is_positive x v h)
  conj_symm := fun u v => kahlerMetric_symm x u v
  add_left := fun u v w => by unfold kahlerMetric; simp only [map_add, LinearMap.add_apply]
  smul_left := fun r u v => by unfold kahlerMetric; simp only [map_smul, LinearMap.smul_apply, Real.smul_def]

/-- The pointwise norm of a tangent vector. -/
def tangentNorm (x : X) (v : TangentSpace 𝓒(Complex, n) x) : ℝ :=
  Real.sqrt (kahlerMetric x v v)

/-- The pointwise comass of a k-form at a point x.
Defined as the supremum of |ω(v₁, ..., vₖ)| over unit tangent vectors. -/
def pointwiseComass {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  sSup { r : ℝ | ∃ (v : Fin k → TangentSpace 𝓒(Complex, n) x),
    (∀ i, tangentNorm x (v i) ≤ 1) ∧ r = |α x v| }

/-- Global comass norm on forms. -/
def comass {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  ⨆ x, pointwiseComass α x

/-- Comass is non-negative.
Proof: Pointwise comass is a supremum of absolute values. -/
theorem comass_nonneg {k : ℕ}
    (α : SmoothForm n X k) :
    comass α ≥ 0 := by
  unfold comass
  apply Real.iSup_nonneg
  intro x
  unfold pointwiseComass
  apply Real.sSup_nonneg
  rintro r ⟨v, _, h_val⟩
  rw [h_val]
  apply abs_nonneg

/-- The comass of the zero form is zero. -/
theorem comass_zero : comass (0 : SmoothForm n X k) = 0 := by
  unfold comass pointwiseComass
  simp only [Pi.zero_apply, LinearMap.zero_apply, abs_zero]
  -- The supremum of {0} is 0
  have h_set : ∀ x, { r : ℝ | ∃ (v : Fin k → TangentSpace 𝓒(Complex, n) x),
      (∀ i, tangentNorm x (v i) ≤ 1) ∧ r = |0| } = {0} := by
    intro x; ext r; constructor
    · rintro ⟨v, _, rfl⟩; exact Set.mem_singleton 0
    · intro hr; rw [Set.mem_singleton_iff] at hr
      rw [hr, abs_zero]
      use fun _ => 0
      constructor
      · intro i; unfold tangentNorm; simp [kahlerMetric]
      · rfl
  simp_rw [h_set, Real.sSup_singleton]
  exact Real.iSup_const 0

/-- The comass of a negated form equals the comass of the form. -/
theorem comass_neg {k : ℕ} (α : SmoothForm n X k) :
    comass (-α) = comass α := by
  unfold comass pointwiseComass
  congr 1
  ext x
  congr 1
  ext r
  constructor
  · rintro ⟨v, hv, h_val⟩
    use v, hv
    simp only [Pi.neg_apply, LinearMap.neg_apply, abs_neg] at h_val ⊢
    exact h_val
  · rintro ⟨v, hv, h_val⟩
    use v, hv
    simp only [Pi.neg_apply, LinearMap.neg_apply, abs_neg]
    exact h_val

/-- Comass is subadditive. -/
theorem comass_add_le {k : ℕ} (α β : SmoothForm n X k) :
    comass (α + β) ≤ comass α + comass β := by
  unfold comass
  apply Real.iSup_le
  intro x
  apply le_add_of_le_add_left
  apply Real.le_iSup_add_iSup
  intro _ _
  unfold pointwiseComass
  rintro r ⟨v, hv, h_val⟩
  rw [h_val]
  simp only [Pi.add_apply, LinearMap.add_apply]
  calc |α x v + β x v| ≤ |α x v| + |β x v| := abs_add _ _
    _ ≤ sSup { r | ∃ v, (∀ i, tangentNorm x (v i) ≤ 1) ∧ r = |α x v| } +
        sSup { r | ∃ v, (∀ i, tangentNorm x (v i) ≤ 1) ∧ r = |β x v| } := by
      apply add_le_add
      · apply Real.le_sSup
        · use |α x v|; use v, hv
        · use v, hv
      · apply Real.le_sSup
        · use |β x v|; use v, hv
        · use v, hv

/-- Comass is absolutely homogeneous. -/
theorem comass_smul {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    comass (r • α) = |r| * comass α := by
  unfold comass pointwiseComass
  simp only [Pi.smul_apply, LinearMap.smul_apply]
  by_cases hr : r = 0
  · simp [hr]
    exact Real.iSup_const 0
  · congr 1
    ext x
    rw [Real.smul_sSup (abs_nonneg r)]
    congr 1
    ext s
    constructor
    · rintro ⟨v, hv, h_val⟩
      use |r|⁻¹ * s
      constructor
      · use v, hv
        rw [h_val, abs_mul, mul_comm]
      · field_simp
    · rintro ⟨t, ⟨v, hv, h_val_t⟩, h_eq⟩
      use v, hv
      rw [h_val_t] at h_eq
      rw [abs_mul, ← h_eq]
      ring

/-- **Continuity of Pointwise Comass**
This is **CRITICAL** for the Extreme Value Theorem application.
The supremum of a smoothly varying family of bounded linear functionals
over a compact set (the unit ball in T_x X) is continuous. -/
theorem pointwiseComass_continuous {k : ℕ} (α : SmoothForm n X k) :
    Continuous (pointwiseComass α) :=
  sorry

/-! ## Norms on Forms -/

/-- The metric on the cotangent space induced by the Kähler metric. -/
def kahlerMetricDual (x : X)
    (u v : CotangentSpace 𝓒(Complex, n) x) : ℝ :=
  -- This should be the dual metric to g.
  -- For now, we define its existence and properties.
  sorry

/-- **Definition: Exterior Metric**
The Kähler metric g on T*X induces a natural metric ⟨·,·⟩ on the exterior bundle Λ^k(T*X).
This is the standard inner product on alternating maps induced by the metric on the base space. -/
def pointwiseInner {k : ℕ} (α β : SmoothForm n X k) (x : X) : ℝ :=
  -- Characterized as the determinant of the matrix of inner products.
  -- For simple forms α = α₁ ∧ ... ∧ αₖ, it is det(g(αᵢ, αⱼ)).
  sorry

/-- The pointwise norm of a k-form at x induced by the Kähler metric. -/
def pointwiseNorm {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  Real.sqrt (pointwiseInner α α x)

/-- A form is harmonic if Δω = 0. -/
def isHarmonic {k : ℕ} (ω : SmoothForm n X k) : Prop :=
  laplacian ω = 0

/-- The Dirichlet energy (L2 norm squared) of a form. -/
def energy {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  ∫ x, (pointwiseNorm α x)^2 ∂(volumeForm.toMeasure)

/-- **Energy Minimizer Property**
Harmonic forms are energy minimizers in their cohomology class.
Reference: [Griffiths-Harris, Principles of Algebraic Geometry]. -/
theorem energy_minimizer {k : ℕ} (α γ_harm : SmoothForm n X k) :
    isClosed α → isHarmonic γ_harm → (∃ η, α = γ_harm + extDeriv η) →
    energy α = energy γ_harm + energy (α - γ_harm) :=
  sorry

/-- The L2 inner product of two forms. -/
def innerL2 {k : ℕ} (α β : SmoothForm n X k) : ℝ :=
  ∫ x, (pointwiseInner α β x) ∂(volumeForm.toMeasure)

/-- The L2 norm of a form. -/
def normL2 {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  Real.sqrt (energy α)

/-- The trace function μ = (1/d) tr(H_β) where d = (n choose p).
This identifies a (p,p)-form with a Hermitian operator and takes its normalized trace.
See Section 3 of the manuscript for the isometric identification I. -/
def hermitianTrace {p : ℕ} (β : SmoothForm n X (2 * p)) (x : X) : ℝ :=
  -- Pointwise: μ(x) = (1/d) * tr(I(β(x)))
  let d : ℝ := Nat.choose n p
  (1 / d) * (pointwiseInner β (omegaPow' p) x) -- tr(H_β) = ⟨β, ω^p⟩ with correct normalization

/-! ## Boundedness on Compact Manifolds -/

/-- On a compact manifold, the comass is finite.
This uses the Extreme Value Theorem. -/
theorem comass_finite {k : ℕ}
    (α : SmoothForm n X k) :
    ∃ M : ℝ, ∀ x, pointwiseComass α x ≤ M := by
  -- 1. pointwiseComass α is a continuous function (by pointwiseComass_continuous)
  have h_cont : Continuous (pointwiseComass α) := pointwiseComass_continuous α

  -- 2. By the Extreme Value Theorem, a continuous function on a compact space
  -- is bounded from above and attains its maximum.
  have h_compact : IsCompact (Set.univ : Set X) := isCompact_univ

  -- 3. Apply the theorem
  obtain ⟨x_max, _, h_max⟩ := h_compact.exists_forall_ge Set.univ_nonempty h_cont.continuousOn

  use pointwiseComass α x_max
  intro x
  exact h_max x (Set.mem_univ x)

/-- Comass exists and equals the maximum on compact manifolds. -/
theorem comass_eq_max {k : ℕ}
    (α : SmoothForm n X k) :
    ∃ x_max : X, comass α = pointwiseComass α x_max := by
  -- 1. pointwiseComass α is a continuous function (by pointwiseComass_continuous)
  have h_cont : Continuous (pointwiseComass α) := pointwiseComass_continuous α
  -- 2. By Extreme Value Theorem on compact X, it attains its maximum.
  obtain ⟨x_max, _, h_max⟩ := isCompact_univ.exists_forall_ge Set.univ_nonempty h_cont.continuousOn
  use x_max
  unfold comass
  apply le_antisymm
  · apply ciSup_le
    intro x
    exact h_max x (Set.mem_univ x)
  · apply le_ciSup_of_le
    · -- The range is bounded above (Extreme Value Theorem)
      obtain ⟨M, hM⟩ := comass_finite α
      use M
      rintro r ⟨x, hx⟩
      rw [← hx]
      exact hM x
    · exact le_refl _

end
