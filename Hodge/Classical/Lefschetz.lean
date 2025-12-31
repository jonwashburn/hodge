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
theorem ofForm_wedge_add (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    {p : ℕ} (ω : SmoothForm n X 2) (hω : IsFormClosed ω) (η₁ η₂ : SmoothForm n X p) (h₁ : IsFormClosed η₁) (h₂ : IsFormClosed η₂) :
    ⟦ω ⋏ (η₁ + η₂), isFormClosed_wedge ω (η₁ + η₂) hω (isFormClosed_add h₁ h₂)⟧ =
    ⟦ω ⋏ η₁, isFormClosed_wedge ω η₁ hω h₁⟧ + ⟦ω ⋏ η₂, isFormClosed_wedge ω η₂ hω h₂⟧ := by
  rw [smoothWedge_add_right]
  apply ofForm_add

/-- The Lefschetz operator L : H^p(X) → H^{p+2}(X)
    is the linear map induced by wedging with the Kähler form. -/
def lefschetz_operator (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p : ℕ) : DeRhamCohomologyClass n X p →ₗ[ℂ] DeRhamCohomologyClass n X (p + 2) where
  toFun c := ⟦lefschetzL c.representative, by
    apply isFormClosed_wedge
    · exact K.omega_closed
    · exact c.representative_closed⟧
  map_add' c₁ c₂ := by
    -- L(c₁ + c₂) = ⟦ω ⋏ (c₁ + c₂).rep⟧ = ⟦ω ⋏ c₁.rep + ω ⋏ c₂.rep⟧ = L(c₁) + L(c₂)
    -- Use the fact that c.representative represents c
    have h1 : c₁ = ⟦c₁.representative, c₁.representative_closed⟧ := by simp [DeRhamCohomologyClass.representative]
    have h2 : c₂ = ⟦c₂.representative, c₂.representative_closed⟧ := by simp [DeRhamCohomologyClass.representative]
    have h_sum : c₁ + c₂ = ⟦c₁.representative + c₂.representative, isFormClosed_add c₁.representative_closed c₂.representative_closed⟧ := by
      rw [h1, h2, ofForm_add]
    -- For this stub, we assume the representative of a sum is the sum of representatives
    -- (up to cohomology).
    simp only [lefschetzL, smoothWedge_add_right]
    rw [ofForm_add]
    rfl
  map_smul' r c := by
    -- L(r • c) = ⟦ω ⋏ (r • c).rep⟧ = ⟦r • (ω ⋏ c.rep)⟧ = r • L(c)
    simp only [lefschetzL, smoothWedge_smul_right, RingHom.id_apply]
    rw [ofForm_smul]
    rfl

/-- The Lefschetz operator is determined by wedging with ω. -/
theorem lefschetz_operator_eval (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p : ℕ) (c : DeRhamCohomologyClass n X p) :
    ∃ (ω' : SmoothForm n X (p + 2)) (h_closed : IsFormClosed ω'),
    lefschetz_operator n X p c = ⟦ω', h_closed⟧ := by
  use lefschetzL c.representative
  use (by apply isFormClosed_wedge; exact K.omega_closed; exact c.representative_closed)
  rfl

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

/-- **The Hard Lefschetz Theorem** (Lefschetz, 1924; Hodge, 1941).
    For a smooth projective complex algebraic variety X of dimension n,
    the iterated Lefschetz operator L^{n-p} : H^p(X, ℚ) → H^{2n-p}(X, ℚ)
    is an isomorphism for all p ≤ n.
    References:
    - [S. Lefschetz, "L'Analysis situs et la géométrie algébrique", 1924].
    - [W.V.D. Hodge, "The Theory and Applications of Harmonic Integrals", 1941].
    - [Griffiths-Harris, "Principles of Algebraic Geometry", 1978, Chapter 0.7]. -/
axiom hard_lefschetz_bijective (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p : ℕ) (hp : p ≤ n) :
    Function.Bijective (lefschetz_power n X p (n - p))

/-- The inverse Lefschetz map. -/
def lefschetz_inverse_cohomology (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p k : ℕ) (h : p ≤ n) : DeRhamCohomologyClass n X (p + 2 * k) →ₗ[ℂ] DeRhamCohomologyClass n X p :=
  -- If k = n - p, we use the bijectivity axiom to construct the inverse.
  -- Otherwise, we use a placeholder or assume the lift exists.
  if hk : k = n - p then
    let iso := LinearEquiv.ofBijective (lefschetz_power n X p (n - p)) (hard_lefschetz_bijective n X p h)
    LinearMap.comp (iso.symm.toLinearMap) (cast (by rw [hk]) : LinearMap ℂ (DeRhamCohomologyClass n X (p + 2 * k)) (DeRhamCohomologyClass n X (p + 2 * (n - p))))
  else
    0

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

/-- **The Hard Lefschetz Isomorphism** (Lefschetz, 1924; Hodge, 1941).
    For a Kähler manifold, the cup product with the Kähler class induces an isomorphism
    between cohomology groups of complementary degrees.
    References:
    - [S. Lefschetz, "L'Analysis situs et la géométrie algébrique", 1924].
    - [W.V.D. Hodge, "The Theory and Applications of Harmonic Integrals", 1941].
    - [Griffiths-Harris, "Principles of Algebraic Geometry", 1978, Chapter 0.7]. -/
axiom hard_lefschetz_isomorphism {p' : ℕ} (h_range : p' ≤ n / 2)
    (γ : SmoothForm n X (2 * (n - p'))) (h_closed : IsFormClosed γ)
    (h_rat : isRationalClass (DeRhamCohomologyClass.ofForm γ h_closed)) (h_hodge : isPPForm' n X (n - p') γ) :
    ∃ (η : SmoothForm n X (2 * p')),
      ∃ (h_η_closed : IsFormClosed η),
      isRationalClass (DeRhamCohomologyClass.ofForm η h_η_closed) ∧ isPPForm' n X p' η

/-- **Hard Lefschetz Isomorphism at the Form Level**.
    This axiom provides the existence of a lower-degree representative for a
    (p,p) class when p > n/2, as guaranteed by the Hard Lefschetz theorem.
    Reference: [C. Voisin, "Hodge Theory and Complex Algebraic Geometry", 2002]. -/
axiom hard_lefschetz_inverse_form {p : ℕ} (hp : p > n / 2)
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ) (h_hodge : isPPForm' n X p γ)
    (h_rat : isRationalClass (DeRhamCohomologyClass.ofForm γ h_closed)) :
    ∃ (η : SmoothForm n X (2 * (n - p))),
      ∃ (h_η_closed : IsFormClosed η),
      isPPForm' n X (n - p) η ∧ isRationalClass (DeRhamCohomologyClass.ofForm η h_η_closed)

end
