import Hodge.Basic
import Hodge.Analytic.Forms
import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

noncomputable section

open Classical

universe u

/-!
## Track A.3.1: Hard Lefschetz Theorem
-/

/-- The Lefschetz operator L : H^p(X) → H^{p+2}(X)
    is the linear map induced by wedging with the Kähler form.
    Reference: [Griffiths-Harris, 1978, p. 122]. -/
opaque lefschetz_operator (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p : ℕ) : DeRhamCohomologyClass n X p →ₗ[ℂ] DeRhamCohomologyClass n X (p + 2)

/-- The iterated Lefschetz map L^k : H^p(X) → H^{p+2k}(X). -/
opaque lefschetz_power (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p k : ℕ) : DeRhamCohomologyClass n X p →ₗ[ℂ] DeRhamCohomologyClass n X (p + 2 * k)

/-- **The Hard Lefschetz Theorem** (Lefschetz, 1924). -/
axiom hard_lefschetz_bijective (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p : ℕ) (hp : p ≤ n) :
    Function.Bijective (lefschetz_power n X p (n - p))

/-! ## Hard Lefschetz Isomorphism for Forms -/

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-- **Theorem: Hard Lefschetz Isomorphism at the Form Level** -/
axiom hard_lefschetz_inverse_form {p : ℕ} (hp : p > n / 2)
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ) (h_hodge : isPPForm' n X p γ)
    (h_rat : isRationalClass (DeRhamCohomologyClass.ofForm γ h_closed)) :
    ∃ (η : SmoothForm n X (2 * (n - p))),
      ∃ (h_η_closed : IsFormClosed η),
      isPPForm' n X (n - p) η ∧ isRationalClass (DeRhamCohomologyClass.ofForm η h_η_closed)

/-- **Theorem: Hard Lefschetz Isomorphism (Form Level)** -/
axiom hard_lefschetz_isomorphism' {p' : ℕ} (h_range : p' ≤ n / 2)
    (γ : SmoothForm n X (2 * (n - p'))) (h_closed : IsFormClosed γ)
    (h_rat : isRationalClass (DeRhamCohomologyClass.ofForm γ h_closed)) (h_hodge : isPPForm' n X (n - p') γ) :
    ∃ (η : SmoothForm n X (2 * p')),
      ∃ (h_η_closed : IsFormClosed η),
      isRationalClass (DeRhamCohomologyClass.ofForm η h_η_closed) ∧ isPPForm' n X p' η
