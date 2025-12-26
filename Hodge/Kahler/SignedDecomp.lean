/-!
# Track C.4: Signed Decomposition

This file formalizes the Signed Decomposition Lemma, which states that
any rational Hodge class is a difference of two cone-positive rational Hodge classes.

## Contents
- Form boundedness via Extreme Value Theorem
- Uniform interior radius existence
- Signed Decomposition Lemma (γ = γ⁺ - γ⁻)
- Algebraicity of γ⁻ (complete intersection)

## Status
- [ ] Prove form_is_bounded
- [ ] Prove exists_uniform_interior_radius (move from Cone.lean if needed)
- [ ] Complete signed_decomposition proof
- [ ] Prove omega_pow_is_algebraic
-/

import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Hodge.Kahler.Cone
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [SmoothManifoldWithCorners 𝓒(Complex, n) X] [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-! ## Form Boundedness -/

import Hodge.Analytic.Norms

/-- Any smooth form on a compact manifold has a finite supremum norm. -/
theorem form_is_bounded {k : ℕ} (α : SmoothForm n X k) :
    ∃ M : ℝ, M > 0 ∧ ∀ x, pointwiseComass α x ≤ M := by
  -- 1. pointwiseComass α is continuous
  have h_cont := pointwiseComass_continuous α
  -- 2. X is compact, so pointwiseComass attains its maximum
  obtain ⟨x_max, h_max⟩ := isCompact_univ.exists_forall_ge Set.univ_nonempty h_cont.continuousOn
  let M_max := pointwiseComass α x_max
  use M_max + 1
  constructor
  · -- M_max + 1 > 0 since M_max ≥ 0
    have : 0 ≤ M_max := by
      apply Real.sSup_nonneg
      rintro r ⟨v, _, h_val⟩
      rw [h_val]
      apply abs_nonneg
    linarith
  · intro x
    have : pointwiseComass α x ≤ M_max := h_max x (Set.mem_univ x)
    linarith

/-! ## Signed Decomposition -/

/--
**Lemma: Signed Decomposition** (Lemma 8.7)

Let γ be a rational Hodge class. Then γ = γ⁺ - γ⁻ where γ⁺ and γ⁻ are
cone-positive rational Hodge classes.
-/
theorem signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p))
    (h_hodge : isPPForm' p γ) (h_rational : isRationalClass γ) :
    ∃ (γplus γminus : SmoothForm n X (2 * p)),
      γ = γplus - γminus ∧
      (∀ x, (γplus x) ∈ (stronglyPositiveCone p x : Set (PPFormSpace n X p x))) ∧
      (∀ x, (γminus x) ∈ (stronglyPositiveCone p x : Set (PPFormSpace n X p x))) ∧
      isRationalClass γplus ∧ isRationalClass γminus := by
  -- 1. Get uniform interior radius r₀ > 0
  obtain ⟨r₀, hr₀, h_ball⟩ := exists_uniform_interior_radius (X := X) p
  -- 2. Get bound M > 0 for γ
  obtain ⟨M, hM, h_bound⟩ := form_is_bounded γ
  -- 3. Choose N ∈ ℚ such that N > M / r₀
  have ∃ N : ℚ, (N : ℝ) > M / r₀ := exists_rat_gt (M / r₀)
  obtain ⟨N, hN⟩ := this
  have hN_pos : (N : ℝ) > 0 := by
    apply lt_trans _ hN
    apply div_pos hM hr₀

  -- 4. Define γminus = N • ω^p
  let γminus := (N : ℝ) • (omegaPow' p) -- Assuming omegaPow' exists as a form
  -- 5. Define γplus = γ + γminus
  let γplus := γ + γminus

  -- 6. Check γ = γplus - γminus
  use γplus, γminus
  constructor
  · simp only [add_sub_cancel_right]

  -- 7. Check cone-positivity of γplus and γminus
  constructor
  · intro x
    -- We need to show γplus(x) = γ(x) + N·ω^p(x) ∈ K_p(x).
    -- Since K_p(x) is a cone and N > 0, this is equivalent to:
    -- (1/N)·γ(x) + ω^p(x) ∈ K_p(x).
    -- By choice of N, ‖(1/N)·γ(x)‖ = (1/N)‖γ(x)‖ ≤ M/N < r₀.
    -- Thus (1/N)·γ(x) + ω^p(x) ∈ Metric.ball (omegaPow p x) r₀.
    -- By h_ball, Metric.ball (omegaPow p x) r₀ ⊆ K_p(x).
    have h_in_ball : (1 / (N : ℝ)) • γ x + (omegaPow p x).val ∈ Metric.ball (omegaPow p x).val r₀ := by
      simp [Metric.mem_ball, dist_eq_norm]
      rw [add_sub_cancel_right]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (show (0 : ℝ) < N from hN_pos)]
      calc (1 / (N : ℝ)) * pointwiseComass γ x ≤ (1 / (N : ℝ)) * M := by
          apply mul_le_mul_of_nonneg_left (h_bound x) (by apply inv_nonneg.mpr; exact le_of_lt hN_pos)
        _ < r₀ := by
          rw [mul_comm, ← div_eq_mul_inv]
          exact (lt_div_iff hN_pos).mp hN

    have h_in_cone : (1 / (N : ℝ)) • γ x + (omegaPow p x).val ∈ (stronglyPositiveCone p x : Set (PPFormSpace n X p x)) := by
      apply h_ball x
      exact h_in_ball

    -- Since K_p(x) is a cone, N • ((1/N)•γ(x) + ω^p(x)) ∈ K_p(x)
    have : (N : ℝ) • ((1 / (N : ℝ)) • γ x + (omegaPow p x).val) ∈ (stronglyPositiveCone p x : Set (PPFormSpace n X p x)) := by
      apply (stronglyPositiveCone p x).smul_mem
      · exact le_of_lt hN_pos
      · exact h_in_cone

    simp [smul_add] at this
    exact this

  · intro x
    -- γminus(x) = N·ω^p(x).
    -- ω^p(x) ∈ interior(K_p(x)) ⊆ K_p(x).
    -- Since K_p(x) is a cone and N > 0, N·ω^p(x) ∈ K_p(x).
    have h_interior : (omegaPow p x) ∈ interior (stronglyPositiveCone p x : Set (PPFormSpace n X p x)) :=
      omegaPow_in_interior p x
    have h_cone : (omegaPow p x) ∈ (stronglyPositiveCone p x : Set (PPFormSpace n X p x)) :=
      interior_subset h_interior
    apply (stronglyPositiveCone p x).smul_mem
    · exact le_of_lt hN_pos
    · exact h_cone

  -- 8. Check rationality
  constructor
  · -- γ is rational, γminus is rational (multiple of rational class ω^p)
    -- The sum of rational classes is rational.
    apply isRationalClass_add h_rational
    apply isRationalClass_smul_rat N
    -- ω^p is rational
    apply isRationalClass_pow p omega_is_rational
  · -- γminus = N·ω^p is rational because [ω^p] is rational and N ∈ ℚ.
    apply isRationalClass_smul_rat N
    apply isRationalClass_pow p omega_is_rational

/-- The class [ω^p] is algebraic (represented by a complete intersection).
Reference: [Kodaira, 1954]. -/
theorem omega_pow_is_algebraic {p : ℕ} :
    ∃ (Z : Set X), isAlgebraicSubvariety Z ∧ FundamentalClass Z = (omegaPow' (n := n) (X := X) p) := by
  -- 1. On a projective manifold X ↪ ℂP^N, the Kähler form ω is the restriction of
  --    the Fubini-Study form ω_FS from the ambient projective space.
  -- 2. The cohomology class [ω_FS] is the first Chern class of the line bundle O(1).
  -- 3. A generic section of O(1) defines a hyperplane section H, which is an 
  --    algebraic hypersurface.
  -- 4. The intersection of p generic hyperplane sections H₁ ∩ ... ∩ H_p is an 
  --    algebraic subvariety Z of codimension p.
  -- 5. The fundamental class of Z is exactly the p-th power of the Kähler class.
  -- Reference: [Griffiths-Harris, 1978].
  sorry

end
