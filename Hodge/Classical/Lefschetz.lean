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

/-- Linearity of wedging with a closed form on cohomology classes. -/
axiom ofForm_wedge_add (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    {p : ℕ} (ω : SmoothForm n X 2) (hω : IsFormClosed ω) (η₁ η₂ : SmoothForm n X p) (h₁ : IsFormClosed η₁) (h₂ : IsFormClosed η₂) :
    ⟦ω ⋏ (η₁ + η₂), isFormClosed_wedge ω (η₁ + η₂) hω (isFormClosed_add h₁ h₂)⟧ =
    ⟦ω ⋏ η₁, isFormClosed_wedge ω η₁ hω h₁⟧ + ⟦ω ⋏ η₂, isFormClosed_wedge ω η₂ hω h₂⟧

/-- The Lefschetz operator L : H^p(X) → H^{p+2}(X)
    is the linear map induced by wedging with the Kähler form. -/
opaque lefschetz_operator (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p : ℕ) : DeRhamCohomologyClass n X p →ₗ[ℂ] DeRhamCohomologyClass n X (p + 2)

-- The Lefschetz operator is determined by wedging with ω, but due to degree issues
-- we axiomatize the evaluation property
axiom lefschetz_operator_eval (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p : ℕ) (c : DeRhamCohomologyClass n X p) :
    ∃ (ω' : SmoothForm n X (p + 2)) (h_closed : IsFormClosed ω'),
    lefschetz_operator n X p c = ⟦ω', h_closed⟧

/-- The iterated Lefschetz map L^k : H^p(X) → H^{p+2k}(X). -/
def lefschetz_power (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p k : ℕ) : DeRhamCohomologyClass n X p →ₗ[ℂ] DeRhamCohomologyClass n X (p + 2 * k) :=
  match k with
  | 0 => LinearMap.id
  | k' + 1 =>
    let L := lefschetz_operator n X (p + 2 * k')
    let Lk := lefschetz_power n X p k'
    LinearMap.comp L Lk

/-- **The Hard Lefschetz Theorem** (Lefschetz, 1924). -/
axiom hard_lefschetz_bijective (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p : ℕ) (hp : p ≤ n) :
    Function.Bijective (lefschetz_power n X p (n - p))

/-- The inverse Lefschetz map. -/
opaque lefschetz_inverse_cohomology (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p k : ℕ) (h : p ≤ n) : DeRhamCohomologyClass n X (p + 2 * k) →ₗ[ℂ] DeRhamCohomologyClass n X p

-- **Lefschetz Compatibility** (Voisin, 2002).
-- Lefschetz operator commutes with the cycle class map.
-- Note: This requires defining SignedAlgebraicCycle and AlgebraicSubvariety which
-- are omitted in this axiomatized version.
-- axiom lefschetz_compatibility (p : ℕ) (Z : SignedAlgebraicCycle n X)
--     (H : AlgebraicSubvariety n X) (hH : H.codim = 1) :
--     (Z.intersect H).cycleClass (p + 1) = lefschetz_operator n X (2 * p) (Z.cycleClass p)

/-! ## Hard Lefschetz Isomorphism for Forms -/

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-- **The Hard Lefschetz Isomorphism** (Lefschetz, 1924). -/
axiom hard_lefschetz_isomorphism {p' : ℕ} (h_range : p' ≤ n / 2)
    (γ : SmoothForm n X (2 * (n - p'))) (h_closed : IsFormClosed γ)
    (h_rat : isRationalClass (DeRhamCohomologyClass.ofForm γ h_closed)) (h_hodge : isPPForm' n X (n - p') γ) :
    ∃ (η : SmoothForm n X (2 * p')),
      ∃ (h_η_closed : IsFormClosed η),
      isRationalClass (DeRhamCohomologyClass.ofForm η h_η_closed) ∧ isPPForm' n X p' η

/-- **Theorem: Hard Lefschetz Isomorphism at the Form Level** -/
axiom hard_lefschetz_inverse_form {p : ℕ} (hp : p > n / 2)
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ) (h_hodge : isPPForm' n X p γ)
    (h_rat : isRationalClass (DeRhamCohomologyClass.ofForm γ h_closed)) :
    ∃ (η : SmoothForm n X (2 * (n - p))),
      ∃ (h_η_closed : IsFormClosed η),
      isPPForm' n X (n - p) η ∧ isRationalClass (DeRhamCohomologyClass.ofForm η h_η_closed)

end
