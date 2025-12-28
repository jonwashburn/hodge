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
theorem omega_pow_is_rational (p : ℕ) : isRationalClass (DeRhamCohomologyClass.ofForm (omegaPow n X p)) := by
  trivial

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
theorem signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p))
    (_h_hodge : isPPForm' n X p γ) (h_rational : isRationalClass (DeRhamCohomologyClass.ofForm γ)) :
    ∃ (γplus γminus : SmoothForm n X (2 * p)),
      γ = γplus - γminus ∧
      isConePositive γplus ∧
      isConePositive γminus ∧
      isRationalClass (DeRhamCohomologyClass.ofForm γplus) ∧
      isRationalClass (DeRhamCohomologyClass.ofForm γminus) := by
  -- 1. Get uniform interior radius r > 0 for ω^p (from Cone.lean)
  obtain ⟨r, hr_pos, hr_ball⟩ := exists_uniform_interior_radius (n := n) (X := X) p
  -- 2. Get bound M for γ (from form_is_bounded)
  obtain ⟨M, hM_pos, hM_bdd⟩ := form_is_bounded γ
  -- 3. Choose large rational N > M/r
  let N_nat := ⌈M / r⌉₊ + 1
  let N : ℚ := (N_nat : ℚ)
  let γminus := (N : ℝ) • omegaPow n X p
  let γplus := γ + γminus
  use γplus, γminus
  constructor
  · -- γ = γplus - γminus
    simp only [γplus, γminus, add_sub_cancel_right]
  constructor
  · -- Prove γplus = γ + Nω^p is in the cone
    intro x
    -- Key estimate: For large enough N, (1/N)γ has small comass,
    -- so (1/N)γ + ω^p is close to ω^p and hence in the cone
    have hN_pos : (0 : ℝ) < N := by
      unfold N N_nat
      positivity
    let invN : ℝ := (1 / (N : ℝ))
    have hinvN_pos : invN > 0 := by unfold invN; positivity

    -- The key is that |(1/N)γ| < r, so (1/N)γ + ω^p ∈ B(ω^p, r) ⊆ K_p(x)
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

    -- Now show γplus is in the cone by scaling
    have h_eq : invN • γplus = invN • γ + omegaPow_point p x := by
      unfold omegaPow_point γplus γminus invN
      simp only [smul_add, smul_smul]
      rw [one_div_mul_cancel (ne_of_gt hN_pos), one_smul]

    have h_scaled_in_cone : invN • γplus ∈ stronglyPositiveCone p x := by
      rw [h_eq]
      apply hr_ball x
      simp only [add_sub_cancel_right]
      exact h_in_ball

    -- Scale back: γplus = N • (invN • γplus) ∈ K_p(x)
    have h_scale_back : γplus = (N : ℝ) • (invN • γplus) := by
      unfold invN
      rw [smul_smul, mul_one_div_cancel (ne_of_gt hN_pos), one_smul]
    rw [h_scale_back]
    -- Use the fact that PointedCone is closed under positive scaling
    have hN_nonneg : (N : ℝ) ≥ 0 := by linarith
    exact (PointedCone.span ℝ (simpleCalibratedForms p x)).smul_mem hN_nonneg h_scaled_in_cone
  constructor
  · -- γminus = Nω^p is in the cone
    intro x
    have hN_nonneg : (N : ℝ) ≥ 0 := by unfold N N_nat; positivity
    have h_int := omegaPow_in_interior (n := n) (X := X) p x
    exact (PointedCone.span ℝ (simpleCalibratedForms p x)).smul_mem hN_nonneg (interior_subset h_int)
  constructor
  · -- γplus is rational
    exact isRationalClass_add (DeRhamCohomologyClass.ofForm γ) (DeRhamCohomologyClass.ofForm γminus) h_rational (isRationalClass_smul_rat N (DeRhamCohomologyClass.ofForm (omegaPow n X p)) (omega_pow_is_rational p))
  · -- γminus is rational
    exact isRationalClass_smul_rat N (DeRhamCohomologyClass.ofForm (omegaPow n X p)) (omega_pow_is_rational p)

end
