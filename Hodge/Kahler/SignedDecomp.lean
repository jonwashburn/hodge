/-!
# Track C.4: Signed Decomposition
-/

import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Hodge.Kahler.Cone
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Hodge.Analytic.Norms

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [SmoothManifoldWithCorners 𝓒(Complex, n) X] [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-! ## Form Boundedness -/

/-- Any smooth form on a compact manifold has a finite supremum norm. -/
theorem form_is_bounded {k : ℕ} (α : SmoothForm n X k) :
    ∃ M : ℝ, M > 0 ∧ ∀ x, pointwiseComass α x ≤ M := by
  have h_cont := pointwiseComass_continuous α
  obtain ⟨x_max, h_max⟩ := isCompact_univ.exists_forall_ge Set.univ_nonempty h_cont.continuousOn
  use pointwiseComass α x_max + 1
  constructor
  · have : 0 ≤ pointwiseComass α x_max := by
      apply Real.sSup_nonneg
      rintro r ⟨v, _, rfl⟩; apply abs_nonneg
    linarith
  · intro x; have h := h_max x (Set.mem_univ x); linarith

/-! ## Signed Decomposition -/

/-- **Lemma: Signed Decomposition** (Lemma 8.7)
Let γ be a rational Hodge class. Then γ = γ⁺ - γ⁻ where γ⁺ and γ⁻ are
cone-positive rational Hodge classes. -/
theorem signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p))
    (h_hodge : isPPForm' p γ) (h_rational : isRationalClass γ) :
    ∃ (γplus γminus : SmoothForm n X (2 * p)),
      γ = γplus - γminus ∧
      isConePositive γplus ∧
      isConePositive γminus ∧
      isRationalClass γplus ∧ isRationalClass γminus := by
  -- 1. Get uniform interior radius r₀ > 0 for the Kähler form ω^p.
  obtain ⟨r₀, hr₀, h_ball⟩ := exists_uniform_interior_radius (X := X) p
  -- 2. Get bound M > 0 for the Hodge class representative γ.
  obtain ⟨M, hM, h_bound⟩ := form_is_bounded γ
  -- 3. Choose a large rational number N such that N > M / r₀.
  have ∃ N : ℚ, (N : ℝ) > M / r₀ := exists_rat_gt (M / r₀)
  obtain ⟨N, hN⟩ := this
  have hN_pos : (N : ℝ) > 0 := lt_trans (div_pos hM hr₀) hN

  -- 4. Define γminus = N • ω^p.
  let γminus := (N : ℝ) • (omegaPow (n := n) (X := X) p)
  -- 5. Define γplus = γ + γminus.
  let γplus := γ + γminus

  use γplus, γminus
  constructor
  · simp only [add_sub_cancel_right]
  · constructor
    · intro x
      -- 6. Verify γplus is cone-positive: (1/N)γ(x) + ω^p(x) lies in K_p(x).
      -- Since ‖(1/N)γ(x)‖ < r₀, it lies in the r₀-ball around ω^p(x).
      sorry
    · constructor
      · intro x
        -- 7. Verify γminus is cone-positive: N > 0 and ω^p(x) is in the interior.
        sorry
      · constructor
        · -- 8. Verify rationality of γplus.
          apply isRationalClass_add h_rational
          apply isRationalClass_smul_rat N
          apply isRationalClass_pow p omega_is_rational
        · -- 9. Verify rationality of γminus.
          apply isRationalClass_smul_rat N
          apply isRationalClass_pow p omega_is_rational

/-- The class [ω^p] is algebraic (represented by a complete intersection).
Reference: [Kodaira, 1954]. -/
theorem omega_pow_is_algebraic {p : ℕ} :
    ∃ (Z : Set X), isAlgebraicSubvariety Z ∧ FundamentalClass Z = (omegaPow p) := by
  -- Follows from the fact that ω represents the hyperplane class in CP^N.
  sorry

end
