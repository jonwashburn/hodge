import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Hodge.Kahler.Cone
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Hodge.Analytic.Norms
import Mathlib.Algebra.Order.Field.Basic

/-!
# Track C.4: Signed Decomposition

This file proves the signed decomposition theorem for rational Hodge classes.
-/

noncomputable section

open Classical Set Filter

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-! ## Form Boundedness -/

/-- Any smooth form on a compact manifold has a finite supremum norm. -/
axiom form_is_bounded_axiom {k : ℕ} (α : SmoothForm n X k) :
    ∃ M : ℝ, M > 0 ∧ ∀ x, pointwiseComass α x ≤ M

theorem form_is_bounded {k : ℕ} (α : SmoothForm n X k) :
    ∃ M : ℝ, M > 0 ∧ ∀ x, pointwiseComass α x ≤ M :=
  form_is_bounded_axiom α

/-! ## Helper lemmas for rationality -/

/-- ω^p is a rational class. -/
theorem omega_pow_is_rational_SD (p : ℕ) : isRationalClass ⟦omegaPow n X p, omega_pow_isClosed p⟧ :=
  omega_pow_is_rational p

/-! ## Signed Decomposition -/

/-- **Lemma: Signed Decomposition** (Lemma 8.7)
    Let γ be a rational Hodge class. Then γ = γ⁺ - γ⁻ where γ⁺ and γ⁻ are
    cone-positive rational Hodge classes. -/
structure SignedDecomposition {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ) where
  γplus : SmoothForm n X (2 * p)
  γminus : SmoothForm n X (2 * p)
  N : ℚ
  h_plus_closed : IsFormClosed γplus
  h_minus_closed : IsFormClosed γminus
  h_eq : γ = γplus - γminus
  h_plus_cone : isConePositive γplus
  h_minus_cone : isConePositive γminus
  h_plus_rat : isRationalClass ⟦γplus, h_plus_closed⟧
  h_minus_rat : isRationalClass ⟦γminus, h_minus_closed⟧
  h_N_pos : N > 0
  h_gamma_minus : γminus = (N : ℝ) • omegaPow n X p

/-- **Theorem: Signed Decomposition** (Lemma 8.7)
    Given a representative form γ of a rational Hodge class, there exists a signed
    decomposition of γ. This is Lemma 8.7 in the manuscript. -/
noncomputable def signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (_h_hodge : isPPForm' n X p γ) (h_rational : isRationalClass ⟦γ, h_closed⟧) :
    SignedDecomposition γ h_closed :=
  let h_radius_exists := exists_uniform_interior_radius (n := n) (X := X) (K := K) p
  let r := Classical.choose h_radius_exists
  let hr_pos := (Classical.choose_spec h_radius_exists).1
  let hr_ball := (Classical.choose_spec h_radius_exists).2

  let h_bdd_exists := form_is_bounded γ
  let M := Classical.choose h_bdd_exists
  let hM_pos := (Classical.choose_spec h_bdd_exists).1
  let hM_bdd := (Classical.choose_spec h_bdd_exists).2

  let h_arch_exists := exists_rat_gt (M / r)
  let N := Classical.choose h_arch_exists
  let hN := Classical.choose_spec h_arch_exists

  let hN_pos : N > 0 := by
    have hMr_pos : M / r > 0 := div_pos hM_pos hr_pos
    have hN_real_pos : (N : ℝ) > 0 := lt_trans hMr_pos hN
    exact_mod_cast hN_real_pos

  let γminus : SmoothForm n X (2 * p) := (N : ℝ) • omegaPow n X p
  let γplus : SmoothForm n X (2 * p) := γ + γminus

  let h_plus_closed : IsFormClosed γplus := by
    unfold IsFormClosed
    rw [smoothExtDeriv_add, smoothExtDeriv_smul (n := n) (X := X) (k := 2 * p) (N : ℂ)]
    have h_omega_closed : IsFormClosed (omegaPow n X p) := omega_pow_isClosed p
    rw [h_closed, h_omega_closed]
    simp

  let h_minus_closed : IsFormClosed γminus := by
    unfold IsFormClosed
    rw [smoothExtDeriv_smul (n := n) (X := X) (k := 2 * p) (N : ℂ)]
    have h_omega_closed : IsFormClosed (omegaPow n X p) := omega_pow_isClosed p
    rw [h_omega_closed]
    simp

  { γplus := γplus,
    γminus := γminus,
    N := N,
    h_plus_closed := h_plus_closed,
    h_minus_closed := h_minus_closed,
    h_eq := by simp [γplus, add_sub_cancel_right],
    h_plus_cone := by
      unfold isConePositive
      intro x
      let y := (N⁻¹ : ℝ) • γplus
      have h_y_cone : y ∈ stronglyPositiveCone p x := by
        apply hr_ball x y
        have : y - omegaPow_point p x = (N⁻¹ : ℝ) • γ := by
          unfold y
          ext x' v'
          simp [γplus, γminus, omegaPow_point]
          have hN_ne : (N : ℝ) ≠ 0 := by norm_cast; exact hN_pos.ne'
          field_simp [hN_ne]
          ring
        rw [this]
        rw [pointwiseComass_smul (n := n) (X := X) (k := 2 * p)]
        have hN_inv_pos : (N⁻¹ : ℝ) > 0 := by
          norm_cast; exact inv_pos.mpr hN_pos
        rw [abs_of_pos hN_inv_pos]
        calc (N⁻¹ : ℝ) * pointwiseComass γ x
          _ ≤ (N⁻¹ : ℝ) * M := mul_le_mul_of_nonneg_left (hM_bdd x) hN_inv_pos.le
          _ < r := by
            rw [inv_mul_lt_iff (by norm_cast; exact hN_pos)]
            rw [← div_lt_iff hr_pos] at hN
            exact hN
      have h_γplus_eq : γplus = (N : ℝ) • y := by
        unfold y
        rw [smul_smul]
        have h_mul : (N : ℝ) * (N⁻¹ : ℝ) = 1 := by
          norm_cast
          exact mul_inv_cancel (by exact hN_pos.ne')
        rw [h_mul, one_smul]
      rw [h_γplus_eq]
      unfold stronglyPositiveCone
      have h_cone := PointedCone.span ℝ (simpleCalibratedForms p x)
      apply h_cone.smul_mem
      · norm_cast; exact hN_pos.le
      · exact h_y_cone,
    h_minus_cone := by
      unfold isConePositive
      intro x
      unfold stronglyPositiveCone
      have h_cone := PointedCone.span ℝ (simpleCalibratedForms p x)
      apply h_cone.smul_mem
      · norm_cast; exact hN_pos.le
      · have h_int := omegaPow_in_interior (n := n) (X := X) p x
        exact interior_subset h_int,
    h_plus_rat := by
      have h_sum : ⟦γplus, h_plus_closed⟧ = ⟦γ, h_closed⟧ + ⟦γminus, h_minus_closed⟧ := by
        rw [← ofForm_add (n := n) (X := X) (k := 2 * p)]
        apply ofForm_proof_irrel
      rw [h_sum]
      have h_γminus_rat : isRationalClass ⟦γminus, h_minus_closed⟧ := by
        have h_omega_rat := omega_pow_is_rational_SD p
        have h_eq : ⟦γminus, h_minus_closed⟧ = (N : ℚ) • ⟦omegaPow n X p, omega_pow_isClosed p⟧ := by
          rw [← ofForm_smul_rat (n := n) (X := X) (k := 2 * p)]
          apply ofForm_proof_irrel
        rw [h_eq]
        exact isRationalClass_smul_rat N _ h_omega_rat
      exact isRationalClass_add _ _ h_rational h_γminus_rat,
    h_minus_rat := by
      have h_omega_rat := omega_pow_is_rational_SD p
      have h_eq : ⟦γminus, h_minus_closed⟧ = (N : ℚ) • ⟦omegaPow n X p, omega_pow_isClosed p⟧ := by
        rw [← ofForm_smul_rat (n := n) (X := X) (k := 2 * p)]
        apply ofForm_proof_irrel
      rw [h_eq]
      exact isRationalClass_smul_rat N _ h_omega_rat,
    h_N_pos := hN_pos,
    h_gamma_minus := rfl }

end
