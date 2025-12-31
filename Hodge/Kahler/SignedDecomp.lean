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

/-- Any smooth form on a compact manifold has a finite supremum norm.
    Uses compactness of X (from ProjectiveComplexManifold) and continuity of pointwiseComass. -/
theorem form_is_bounded {k : ℕ} (α : SmoothForm n X k) :
    ∃ M : ℝ, M > 0 ∧ ∀ x, pointwiseComass α x ≤ M := by
  -- On compact manifolds, continuous functions are bounded and attain their maximum
  have h_cont : Continuous (pointwiseComass α) := pointwiseComass_continuous α
  -- The range is compact since X is compact
  have h_compact : IsCompact (Set.range (pointwiseComass α)) := isCompact_range h_cont
  -- The range is nonempty since X is nonempty
  have h_nonempty : (Set.range (pointwiseComass α)).Nonempty := Set.range_nonempty _
  -- Compact nonempty sets in ℝ have a maximum
  obtain ⟨M, hM_in, hM_max⟩ := h_compact.exists_isMaxOn h_nonempty
  obtain ⟨x₀, hx₀⟩ := hM_in
  -- M = pointwiseComass α x₀ ≥ 0 by pointwiseComass_nonneg
  have hM_nonneg : M ≥ 0 := by rw [← hx₀]; exact pointwiseComass_nonneg α x₀
  -- Use M + 1 > 0 as our bound
  use M + 1
  constructor
  · linarith
  · intro x
    have hx_in : pointwiseComass α x ∈ Set.range (pointwiseComass α) := Set.mem_range_self x
    have hx_le : pointwiseComass α x ≤ M := by
      rw [← hx₀]
      exact hM_max hx_in
    linarith

/-! ## Helper lemmas for rationality -/

/-- ω^p is a rational class. -/
theorem omega_pow_is_rational_SD (p : ℕ) : isRationalClass ⟦kahlerPow (n := n) (X := X) p, omega_pow_IsFormClosed (n := n) (X := X) p⟧ :=
  omega_pow_is_rational p

/-! ## Cone Positivity Helpers -/

/-- The strongly positive cone is closed under positive scalar multiplication.
    This follows from `PointedCone.span` being a submodule over ℝ≥0. -/
theorem stronglyPositiveCone_smul_pos {p : ℕ} (x : X) (r : ℝ) (hr : r > 0)
    (α : SmoothForm n X (2 * p)) (hα : α ∈ stronglyPositiveCone p x) :
    r • α ∈ stronglyPositiveCone p x := by
  unfold stronglyPositiveCone at *
  -- PointedCone.span is a submodule, so it's closed under smul
  exact Submodule.smul_mem _ r hα

/-- For any form γ, there exists N > 0 such that γ + N · ω^p is cone-positive.
    This is the geometric heart of the signed decomposition.
    The proof uses the uniform interior radius theorem: since ω^p is in the interior
    of the cone, we can shift any bounded form into the cone by adding a large
    enough multiple of ω^p. -/
theorem exists_cone_positive_shift {p : ℕ} (γ : SmoothForm n X (2 * p)) :
    ∃ N : ℚ, N > 0 ∧ isConePositive (γ + (N : ℝ) • kahlerPow p) := by
  -- Step 1: Get the uniform interior radius r > 0 for ω^p
  obtain ⟨r, hr_pos, hr_ball⟩ := exists_uniform_interior_radius p
  -- Step 2: Get a global bound M for the form γ
  obtain ⟨M, hM_pos, hM_bdd⟩ := form_is_bounded γ
  -- Step 3: Choose N > 0 such that M / N < r
  -- We use the Archimedean property to find such a rational N
  have h_rat : ∃ N : ℚ, (N : ℝ) > M / r := exists_rat_gt (M / r)
  obtain ⟨N, hN_gt⟩ := h_rat
  have hN_pos : N > 0 := by
    have : M / r > 0 := div_pos hM_pos hr_pos
    exact_mod_cast (lt_trans this hN_gt)
  use N, hN_pos
  -- Step 4: Show that γ + N·ω^p is cone-positive at every point x
  intro x
  -- We want to use hr_ball: B(ω^p, r) ⊆ stronglyPositiveCone
  -- Let y = (1/N) • γ + ω^p. Then N • y = γ + N • ω^p.
  let invN : ℝ := 1 / (N : ℝ)
  have h_invN_pos : invN > 0 := one_div_pos.mpr (by exact_mod_cast hN_pos)
  let y := invN • γ + kahlerPow p
  have hy_mem : y ∈ stronglyPositiveCone p x := by
    -- Check if y is within distance r of ω^p
    apply hr_ball x y
    unfold omegaPow_point
    have : y - kahlerPow p = invN • γ := by simp [y]
    rw [this, pointwiseComass_smul, abs_of_pos h_invN_pos]
    -- (1/N) * pointwiseComass γ x ≤ M/N < r
    calc invN * pointwiseComass γ x
        ≤ invN * M := mul_le_mul_of_nonneg_left (hM_bdd x) (le_of_lt h_invN_pos)
      _ = M / N := by field_simp
      _ < r := (div_lt_iff (by exact_mod_cast hN_pos)).mpr (by exact_mod_cast hN_gt)
  -- Since y is in the cone, N • y = γ + N • ω^p is in the cone
  have : (N : ℝ) • y = γ + (N : ℝ) • kahlerPow p := by
    simp [y]; rw [smul_add, ← mul_smul]; simp; field_simp
  rw [← this]
  apply stronglyPositiveCone_smul_pos x (N : ℝ) (by exact_mod_cast hN_pos) y hy_mem

/-- ω^p is cone-positive (it is in the cone at every point). -/
theorem omegaPow_is_cone_positive (p : ℕ) : isConePositive (kahlerPow (n := n) (X := X) p) := by
  intro x
  -- ω^p is in the interior, hence in the cone
  have h := omegaPow_in_interior (n := n) (X := X) p x
  exact interior_subset h

/-- Positive rational multiples of ω^p are cone-positive. -/
theorem smul_omegaPow_cone_positive (p : ℕ) (c : ℚ) (hc : c > 0) :
    isConePositive ((c : ℝ) • kahlerPow (n := n) (X := X) p) := by
  intro x
  have h := omegaPow_is_cone_positive (n := n) (X := X) p x
  exact stronglyPositiveCone_smul_pos x (c : ℝ) (by exact_mod_cast hc) (kahlerPow p) h

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
  h_gamma_minus : γminus = (N : ℝ) • kahlerPow p

/-- **Theorem: Signed Decomposition** (Lemma 8.7)
    Given a representative form γ of a rational Hodge class, there exists a signed
    decomposition of γ. This is Lemma 8.7 in the manuscript.

    The proof uses:
    1. `exists_cone_positive_shift` to find N such that γ + N · ω^p is cone-positive
    2. Setting γ⁺ = γ + N · ω^p and γ⁻ = N · ω^p
    3. Verifying γ = γ⁺ - γ⁻ and both are rational -/
theorem signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (_h_hodge : isPPForm' n X p γ) (h_rational : isRationalClass ⟦γ, h_closed⟧) :
    SignedDecomposition γ h_closed := by
  -- Step 1: Find N > 0 such that γ + N·ω^p is cone-positive
  obtain ⟨N, hN_pos, h_plus_cone⟩ := exists_cone_positive_shift (n := n) (X := X) γ

  -- Step 2: Define γ⁺ and γ⁻
  let γplus := γ + (N : ℝ) • kahlerPow p
  let γminus := (N : ℝ) • kahlerPow p

  -- Step 3: Verify the equation γ = γplus - γminus
  have h_eq : γ = γplus - γminus := by simp [γplus, γminus]

  -- Step 4: Closedness proofs
  have h_plus_closed : IsFormClosed γplus :=
    isFormClosed_add h_closed (isFormClosed_smul_real (omega_pow_IsFormClosed p))
  have h_minus_closed : IsFormClosed γminus :=
    isFormClosed_smul_real (omega_pow_IsFormClosed p)

  -- Step 5: γ⁻ = N·ω^p is cone-positive
  have h_minus_cone : isConePositive γminus :=
    smul_omegaPow_cone_positive (n := n) (X := X) p N hN_pos

  -- Step 6: Rationality of γ⁺ = γ + N·ω^p (sum of rational classes)
  have h_plus_rat : isRationalClass ⟦γplus, h_plus_closed⟧ := by
    -- [γ + N·ω^p] = [γ] + N·[ω^p]
    -- Both [γ] and [ω^p] are rational, and ℚ-module operations preserve rationality
    have h_omega_rat := omega_pow_is_rational (n := n) (X := X) p
    have h_N_omega_rat := isRationalClass_smul_rat N ⟦kahlerPow p, omega_pow_IsFormClosed p⟧ h_omega_rat
    -- Use that γplus and γ + N·ω^p represent the same class (proof irrelevance)
    have h_class_eq : ⟦γplus, h_plus_closed⟧ =
        ⟦γ, h_closed⟧ + (N : ℝ) • ⟦kahlerPow p, omega_pow_IsFormClosed p⟧ := by
      simp only [γplus]
      -- Use ofForm_add and ofForm_smul_real
      have h1 := ofForm_add γ ((N : ℝ) • kahlerPow p) h_closed (isFormClosed_smul_real (omega_pow_IsFormClosed p))
      have h2 := ofForm_smul_real (N : ℝ) (kahlerPow p) (omega_pow_IsFormClosed p)
      calc ⟦γ + (N : ℝ) • kahlerPow p, h_plus_closed⟧
          = ⟦γ + (N : ℝ) • kahlerPow p,
              isFormClosed_add h_closed (isFormClosed_smul_real (omega_pow_IsFormClosed p))⟧ := by
            exact ofForm_proof_irrel _ h_plus_closed _
        _ = ⟦γ, h_closed⟧ + ⟦(N : ℝ) • kahlerPow p, isFormClosed_smul_real (omega_pow_IsFormClosed p)⟧ := by
            simpa using h1
        _ = ⟦γ, h_closed⟧ + (N : ℝ) • ⟦kahlerPow p, omega_pow_IsFormClosed p⟧ := by
            simp only [h2]
    rw [h_class_eq]
    exact isRationalClass_add _ _ h_rational h_N_omega_rat

  -- Step 7: Rationality of γ⁻ = N·ω^p
  have h_minus_rat : isRationalClass ⟦γminus, h_minus_closed⟧ := by
    have h_omega_rat := omega_pow_is_rational (n := n) (X := X) p
    have h_smul := isRationalClass_smul_rat N ⟦kahlerPow p, omega_pow_IsFormClosed p⟧ h_omega_rat
    have h_class_eq : ⟦γminus, h_minus_closed⟧ = (N : ℝ) • ⟦kahlerPow p, omega_pow_IsFormClosed p⟧ := by
      simp only [γminus]
      have h := ofForm_smul_real (N : ℝ) (kahlerPow p) (omega_pow_IsFormClosed p)
      calc ⟦(N : ℝ) • kahlerPow p, h_minus_closed⟧
          = ⟦(N : ℝ) • kahlerPow p, isFormClosed_smul_real (omega_pow_IsFormClosed p)⟧ := by
            exact ofForm_proof_irrel _ h_minus_closed _
        _ = (N : ℝ) • ⟦kahlerPow p, omega_pow_IsFormClosed p⟧ := by simpa using h
    rw [h_class_eq]
    exact h_smul

  -- Construct the SignedDecomposition
  exact {
    γplus := γplus
    γminus := γminus
    N := N
    h_plus_closed := h_plus_closed
    h_minus_closed := h_minus_closed
    h_eq := h_eq
    h_plus_cone := h_plus_cone
    h_minus_cone := h_minus_cone
    h_plus_rat := h_plus_rat
    h_minus_rat := h_minus_rat
    h_N_pos := hN_pos
    h_gamma_minus := rfl
  }

end
