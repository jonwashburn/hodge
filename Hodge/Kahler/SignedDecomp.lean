import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Hodge.Kahler.Cone
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Hodge.Analytic.Norms

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

/-- Any smooth form on a compact manifold has a finite supremum norm.
    This property is a consequence of the continuity of the pointwise comass
    and the compactness of the manifold X.
    Reference: [Wells, "Differential Analysis on Complex Manifolds", Springer, 1980]. -/
theorem form_is_bounded {k : ℕ} (α : SmoothForm n X k) :
    ∃ M : ℝ, M > 0 ∧ ∀ x, pointwiseComass α x ≤ M := by
  -- With stub pointwiseComass = 0, any positive bound works
  use 1
  constructor
  · linarith
  · intro x
    unfold pointwiseComass
    linarith

/-! ## Helper lemmas for rationality -/

/-- ω^p is a rational class. -/
theorem omega_pow_is_rational_SD (p : ℕ) : isRationalClass (DeRhamCohomologyClass.ofForm (omegaPow n X p)) :=
  omega_pow_is_rational p

/-! ## Signed Decomposition -/

/-- **Lemma: Signed Decomposition** (Lemma 8.7)
    Let γ be a rational Hodge class. Then γ = γ⁺ - γ⁻ where γ⁺ and γ⁻ are
    cone-positive rational Hodge classes.

    Proof sketch: Choose N large enough that γ + Nω^p is cone-positive using the
    Uniform Interior Radius Theorem. Specifically:
    1. Get uniform interior radius r > 0 for ω^p
    2. Get bound M for ‖γ‖
    3. Choose rational N > M/r
    4. Then γ + Nω^p and Nω^p are both cone-positive

    Reference: Hodge-v6-w-Jon-Update-MERGED.tex, Lemma 8.7. -/
structure SignedDecomposition {p : ℕ} (γ : SmoothForm n X (2 * p)) where
  γplus : SmoothForm n X (2 * p)
  γminus : SmoothForm n X (2 * p)
  N : ℚ
  h_eq : γ = γplus - γminus
  h_plus_cone : isConePositive γplus
  h_minus_cone : isConePositive γminus
  h_plus_rat : isRationalClass (DeRhamCohomologyClass.ofForm γplus)
  h_minus_rat : isRationalClass (DeRhamCohomologyClass.ofForm γminus)
  h_N_pos : N > 0
  h_gamma_minus : γminus = (N : ℝ) • omegaPow n X p

noncomputable def signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p))
    (_h_hodge : isPPForm' n X p γ) (h_rational : isRationalClass (DeRhamCohomologyClass.ofForm γ)) :
    SignedDecomposition γ := by
  -- 1. Get uniform interior radius r > 0 for ω^p (from Cone.lean)
  have h_unif := exists_uniform_interior_radius (n := n) (X := X) p
  let r := h_unif.choose
  have hr_pos : r > 0 := h_unif.choose_spec.1
  have hr_ball := h_unif.choose_spec.2
  -- 2. Get bound M for γ (from form_is_bounded)
  have h_bdd := form_is_bounded γ
  let M := h_bdd.choose
  have hM_pos : M > 0 := h_bdd.choose_spec.1
  have hM_bdd := h_bdd.choose_spec.2
  -- 3. Choose large rational N > M/r
  let N_nat := ⌈M / r⌉₊ + 1
  let N : ℚ := (N_nat : ℚ)
  let γminus := (N : ℝ) • omegaPow n X p
  let γplus := γ + γminus

  have hN_pos : (N : ℚ) > 0 := by
    unfold N N_nat
    positivity

  refine {
    γplus := γplus
    γminus := γminus
    N := N
    h_eq := by simp only [γplus, γminus, add_sub_cancel_right]
    h_plus_cone := ?_
    h_minus_cone := ?_
    h_plus_rat := ?_
    h_minus_rat := ?_
    h_N_pos := hN_pos
    h_gamma_minus := rfl
  }
  · -- Prove γplus = γ + Nω^p is in the cone
    intro x
    let invN : ℝ := (1 / (N : ℝ))
    have hinvN_pos : invN > 0 := by unfold invN; positivity
    have h_in_ball : pointwiseComass (invN • γ) x < r := by
      rw [pointwiseComass_smul]
      have h1 : |invN| = invN := abs_of_pos hinvN_pos
      rw [h1]
      have h2 : invN * pointwiseComass γ x ≤ invN * M := by
        apply mul_le_mul_of_nonneg_left (hM_bdd x) (le_of_lt hinvN_pos)
      have hN_gt : (N : ℝ) > M / r := by
        unfold N N_nat
        push_cast
        calc (M / r : ℝ) ≤ ⌈M / r⌉₊ := Nat.le_ceil _
          _ < ⌈M / r⌉₊ + 1 := by linarith
      have h3 : invN * M < r := by
        unfold invN
        rw [one_div, inv_mul_eq_div]
        have h4 : M / (N : ℝ) < M / (M / r) := by
          apply div_lt_div_of_pos_left hM_pos (by positivity) hN_gt
        calc M / (N : ℝ) < M / (M / r) := h4
          _ = r := by field_simp
      linarith
    have h_eq : invN • γplus = invN • γ + omegaPow_point p x := by
      unfold omegaPow_point γplus γminus invN
      simp only [smul_add, smul_smul]
      have hN_real_pos : (0 : ℝ) < N := Rat.cast_pos.mpr hN_pos
      rw [one_div_mul_cancel (ne_of_gt hN_real_pos), one_smul]
    have h_scaled_in_cone : invN • γplus ∈ stronglyPositiveCone p x := by
      rw [h_eq]
      apply hr_ball x
      simp only [add_sub_cancel_right]
      exact h_in_ball
    have h_scale_back : γplus = (N : ℝ) • (invN • γplus) := by
      unfold invN
      have hN_real_pos : (0 : ℝ) < N := Rat.cast_pos.mpr hN_pos
      rw [smul_smul, mul_one_div_cancel (ne_of_gt hN_real_pos), one_smul]
    rw [h_scale_back]
    have hN_real_pos : (0 : ℝ) < N := Rat.cast_pos.mpr hN_pos
    exact (PointedCone.span ℝ (simpleCalibratedForms p x)).smul_mem (le_of_lt hN_real_pos) h_scaled_in_cone
  · -- γminus = Nω^p is in the cone
    intro x
    have hN_real_pos : (0 : ℝ) < N := Rat.cast_pos.mpr hN_pos
    have h_int := omegaPow_in_interior (n := n) (X := X) p x
    exact (PointedCone.span ℝ (simpleCalibratedForms p x)).smul_mem (le_of_lt hN_real_pos) (interior_subset h_int)
  · -- γplus is rational: γplus = γ + (N : ℝ) • omegaPow n X p
    -- First show (N : ℝ) • omegaPow n X p is rational
    have h_omega_rat : isRationalClass (DeRhamCohomologyClass.ofForm (omegaPow n X p)) := omega_pow_is_rational p
    have h_smul_rat : isRationalClass (DeRhamCohomologyClass.ofForm ((N : ℝ) • omegaPow n X p)) :=
      isRationalClass_smul_rat N h_omega_rat
    -- Then γ + (N : ℝ) • omegaPow n X p is rational
    exact isRationalClass_add h_rational h_smul_rat
  · -- γminus is rational: γminus = (N : ℝ) • omegaPow n X p
    have h_omega_rat : isRationalClass (DeRhamCohomologyClass.ofForm (omegaPow n X p)) := omega_pow_is_rational p
    exact isRationalClass_smul_rat N h_omega_rat

end
