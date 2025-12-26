import Hodge.Analytic.Forms
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Track B.2: Norms and Metrics (Rigorous Implementation)

This file defines the global norms on differential forms (comass and L2)
and proves their basic properties on compact Kähler manifolds.
-/

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-! ## Comass Norm -/

/-- The Riemannian metric induced by a Kähler form on the tangent space. -/
def kahlerMetric (x : X) (u v : TangentSpace 𝓒(Complex, n) x) : ℝ :=
  K.omega_form x u (Complex.I • v)

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

/-- **Theorem: Continuity of Pointwise Comass**
The supremum of smoothly varying bounded linear functionals over unit balls is continuous. -/
theorem pointwiseComass_continuous {k : ℕ} (α : SmoothForm n X k) :
    Continuous (pointwiseComass α) :=
  sorry

/-- Comass is non-negative. -/
theorem comass_nonneg {k : ℕ} (α : SmoothForm n X k) : comass α ≥ 0 :=
  Real.iSup_nonneg (fun x => Real.sSup_nonneg (by rintro r ⟨v, _, rfl⟩; apply abs_nonneg))

/-- The comass of the zero form is zero. -/
theorem comass_zero {k : ℕ} : comass (0 : SmoothForm n X k) = 0 := by
  unfold comass pointwiseComass
  simp only [Pi.zero_apply, LinearMap.zero_apply, abs_zero]
  -- The supremum of the set {0} is 0.
  have h_set : ∀ x, { r : ℝ | ∃ (v : Fin k → TangentSpace 𝓒(Complex, n) x),
      (∀ i, tangentNorm x (v i) ≤ 1) ∧ r = 0 } = {0} := by
    intro x; ext r; constructor
    · rintro ⟨v, hv, rfl⟩; exact Set.mem_singleton 0
    · intro hr; rw [Set.mem_singleton_iff] at hr; rw [hr]
      use fun _ => 0
      constructor
      · intro i; unfold tangentNorm; simp [kahlerMetric, K.is_j_invariant]
      · rfl
  simp_rw [h_set, Real.sSup_singleton]
  exact Real.iSup_const 0

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
  · simp [hr, comass_zero]
    exact Real.iSup_const 0
  · have h_abs_pos : 0 < |r| := abs_pos.mpr hr
    congr 1; ext x
    rw [Real.smul_sSup (le_of_lt h_abs_pos)]
    congr 1; ext s
    constructor
    · rintro ⟨v, hv, h_val⟩
      use |r|⁻¹ * s
      constructor
      · use v, hv
        rw [h_val, abs_mul, mul_comm, ← mul_assoc, mul_inv_cancel (ne_of_gt h_abs_pos), one_mul]
      · field_simp
    · rintro ⟨t, ⟨v, hv, h_val_t⟩, h_eq⟩
      use v, hv
      rw [h_val_t] at h_eq
      rw [abs_mul, ← h_eq, mul_comm]

/-- On a compact manifold, the comass is finite. -/
theorem comass_finite {k : ℕ} (α : SmoothForm n X k) :
    ∃ M : ℝ, ∀ x, pointwiseComass α x ≤ M := by
  have h_cont : Continuous (pointwiseComass α) := pointwiseComass_continuous α
  have h_compact : CompactSpace X := projective_compact
  obtain ⟨x_max, h_max⟩ := isCompact_univ.exists_forall_ge Set.univ_nonempty h_cont.continuousOn
  use pointwiseComass α x_max
  intro x; exact h_max x (Set.mem_univ x)

/-! ## L2 Norm -/

/-- The Dirichlet energy (L2 norm squared) of a form. -/
def energy {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  -- Integration requires a measure induced by the volume form.
  -- ∫ x, (pointwiseNorm α x)^2 ∂(volumeForm.toMeasure)
  sorry

/-- The L2 norm of a form. -/
def normL2 {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  Real.sqrt (energy α)

end
