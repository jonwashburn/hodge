import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Hodge.Kahler.Cone
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Hodge.Analytic.Norms

/-!
# Track C.4: Signed Decomposition
-/

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-! ## Form Boundedness -/

/-- Any smooth form on a compact manifold has a finite supremum norm. -/
theorem form_is_bounded {k : ℕ} (α : SmoothForm n X k) :
    ∃ M : ℝ, M > 0 ∧ ∀ x, pointwiseComass α x ≤ M := sorry

/-! ## Signed Decomposition -/

/-- **Lemma: Signed Decomposition** (Lemma 8.7)
Let γ be a rational Hodge class. Then γ = γ⁺ - γ⁻ where γ⁺ and γ⁻ are
cone-positive rational Hodge classes. -/
theorem signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p))
    (_h_hodge : isPPForm' p γ) (_h_rational : isRationalClass γ) :
    ∃ (γplus γminus : SmoothForm n X (2 * p)),
      γ = γplus - γminus ∧
      isConePositive γplus ∧
      isConePositive γminus ∧
      isRationalClass γplus ∧ isRationalClass γminus := sorry

end
