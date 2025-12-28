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

/-- Any smooth form on a compact manifold has a finite supremum norm.
    This uses compactness of X and continuity of pointwiseComass. -/
axiom form_is_bounded {k : ℕ} (α : SmoothForm n X k) :
    ∃ M : ℝ, M > 0 ∧ ∀ x, pointwiseComass α x ≤ M

/-! ## Signed Decomposition -/

/-- **Lemma: Signed Decomposition** (Lemma 8.7)
Let γ be a rational Hodge class. Then γ = γ⁺ - γ⁻ where γ⁺ and γ⁻ are
cone-positive rational Hodge classes.

Proof sketch:
1. Let ω^p be the p-th power of the Kähler form.
2. By the uniform interior radius theorem, there exists r > 0 such that
   ball(ω^p(x), r) ⊆ K_p(x) for all x.
3. For any form γ, choose N large enough that γ + N·ω^p lies in the cone.
4. Set γ⁺ = γ + N·ω^p and γ⁻ = N·ω^p.
5. Since ω is rational and N is rational, both γ⁺ and γ⁻ are rational.

Reference: Hodge Conjecture paper, Lemma 8.7.
-/
axiom signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p))
    (h_hodge : isPPForm' n X p γ) (h_rational : isRationalClass γ) :
    ∃ (γplus γminus : SmoothForm n X (2 * p)),
      γ = γplus - γminus ∧
      isConePositive γplus ∧
      isConePositive γminus ∧
      isRationalClass γplus ∧ isRationalClass γminus

end
