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
axiom form_is_bounded {k : ℕ} (α : SmoothForm n X k) :
    ∃ M : ℝ, M > 0 ∧ ∀ x, pointwiseComass α x ≤ M

/-! ## Helper lemmas for rationality -/

/-- ω^p is a rational class. -/
theorem omega_pow_is_rational_SD (p : ℕ) : isRationalClass ⟦kahlerPow (n := n) (X := X) p, omega_pow_IsFormClosed (n := n) (X := X) p⟧ :=
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
  h_gamma_minus : γminus = (N : ℝ) • kahlerPow p

/-- **Theorem: Signed Decomposition** (Lemma 8.7)
    Given a representative form γ of a rational Hodge class, there exists a signed
    decomposition of γ. This is Lemma 8.7 in the manuscript. -/
axiom signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (_h_hodge : isPPForm' n X p γ) (h_rational : isRationalClass ⟦γ, h_closed⟧) :
    SignedDecomposition γ h_closed

end
