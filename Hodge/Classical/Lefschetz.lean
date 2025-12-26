import Hodge.Analytic
import Hodge.Kahler.Manifolds
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [SmoothManifoldWithCorners 𝓒(Complex, n) X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

## Mathematical Statement
For a Kähler manifold (X, ω) of complex dimension n, the map
L^{n-p} : H^p(X) → H^{2n-p}(X) induced by wedging with ω^{n-p}
is an isomorphism for p ≤ n.

## Reference
[Griffiths-Harris, "Principles of Algebraic Geometry", 1978]

## Status
- [x] Define `DeRhamCohomology` as quotient of submodules
- [x] Define `lefschetz_operator` induced by wedge product and its well-definedness
- [x] Define `lefschetz_power` by recursion
- [x] State the axiom
-/

/-- The k-th de Rham cohomology group of X.
Defined as the quotient of closed forms by exact forms. -/
def DeRhamCohomology (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
    [SmoothManifoldWithCorners 𝓒(Complex, n) X] :=
  (closedForms n X k) ⧸ (exactForms n X k).comap (closedForms n X k).subtype

/-! ## Lefschetz Operator -/

/-- Wedging with the Kähler form maps closed forms to closed forms. -/
theorem wedge_kahler_closed {p : ℕ} [K : KahlerManifold n X]
    (α : SmoothForm n X p) (hα : isClosed α) :
    isClosed (α ∧ K.omega_form) := by
  unfold isClosed at *
  rw [d_wedge, hα, kahler_form_closed]
  simp only [wedge, zero_wedge, smul_zero, add_zero]

/-- Wedging with the Kähler form maps exact forms to exact forms. -/
theorem wedge_kahler_exact {p : ℕ} [K : KahlerManifold n X]
    (α : SmoothForm n X p) (hα : isExact α) :
    isExact (α ∧ K.omega_form) := by
  obtain ⟨η, hη⟩ := hα
  use η ∧ K.omega_form
  rw [d_wedge, hη, kahler_form_closed]
  simp only [wedge, smul_zero, add_zero]

/-- The Lefschetz operator L : H^p(X) → H^{p+2}(X)
is the linear map induced by wedging with the Kähler form. -/
def lefschetz_operator {p : ℕ} [K : KahlerManifold n X] :
    DeRhamCohomology n X p →ₗ[ℝ] DeRhamCohomology n X (p + 2) :=
  Quotient.lift (fun α => Quotient.mk _ ⟨α.1 ∧ K.omega_form, wedge_kahler_closed α.1 α.2⟩)
    (by
      intro α₁ α₂ h
      simp only [Submodule.quotientRel_r, Submodule.mem_comap, Submodule.subtype_apply] at h
      rw [Submodule.quotientRel_r, Submodule.mem_comap, Submodule.subtype_apply]
      -- h says α₁ - α₂ is exact. We need to show (α₁ ∧ ω) - (α₂ ∧ ω) is exact.
      -- (α₁ ∧ ω) - (α₂ ∧ ω) = (α₁ - α₂) ∧ ω.
      let diff := α₁ - α₂
      have h_diff_exact : isExact diff.1 := by
        obtain ⟨η, hη⟩ := h
        use η; exact hη
      have h_wedge_exact := wedge_kahler_exact diff.1 h_diff_exact
      obtain ⟨ζ, hζ⟩ := h_wedge_exact
      use ζ
      rw [← hζ]
      simp only [Submodule.coe_sub, Submodule.coe_mk]
      -- Prove (α₁ - α₂) ∧ ω = α₁ ∧ ω - α₂ ∧ ω
      rw [wedge_add, wedge_smul]
      simp only [one_smul, neg_smul]
      rfl)

/-- The iterated Lefschetz map L^k : H^p(X) → H^{p+2k}(X).
Defined recursively by L^0 = Id and L^{k+1} = L ∘ L^k. -/
def lefschetz_power (p k : ℕ) [K : KahlerManifold n X] :
    DeRhamCohomology n X p →ₗ[ℝ] DeRhamCohomology n X (p + 2 * k) :=
  match k with
  | 0 => by
      have h_target : p + 2 * 0 = p := by linarith
      let map := LinearMap.id : DeRhamCohomology n X p →ₗ[ℝ] DeRhamCohomology n X p
      exact cast (by rw [h_target]) map
  | k + 1 => by
      let L := lefschetz_operator (p := p + 2 * k)
      let Lk := lefschetz_power p k
      have h_target : p + 2 * (k + 1) = (p + 2 * k) + 2 := by linarith
      exact cast (by rw [h_target]) (L.comp Lk)

/-! ## Hard Lefschetz Theorem -/

/-- The hypothesis for Hard Lefschetz: a Kähler manifold with a degree. -/
structure HardLefschetzHypothesis (p : ℕ) where
  /-- The degree satisfies p ≤ n -/
  p_le_n : p ≤ n

/-- The conclusion of Hard Lefschetz: L^{n-p} is an isomorphism. -/
structure HardLefschetzConclusion {p : ℕ}
    (hyp : HardLefschetzHypothesis p) where
  /-- The map is bijective -/
  is_bijective : Function.Bijective (lefschetz_power (p := p) (k := n - p))

/-- **Hard Lefschetz Theorem**

For a compact Kähler manifold (X, ω) of complex dimension n,
the map L^{n-p} : H^p(X) → H^{2n-p}(X) is an isomorphism for p ≤ n.

Reference: [Griffiths-Harris, 1978]. -/
theorem hard_lefschetz {p : ℕ} (hyp : HardLefschetzHypothesis p) :
    HardLefschetzConclusion hyp := by
  -- This is a fundamental result in Kähler geometry, derived from the
  -- action of the sl_2(ℝ) algebra on the cohomology of X.
  sorry
