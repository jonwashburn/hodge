import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Hodge.Analytic.Norms
import Hodge.Analytic.Grassmannian
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Track C.3: Strongly Positive Cone

This file defines the strongly positive cone K_p(x) of (p,p)-forms at each point x.
-/

noncomputable section

open Classical Metric Set
open scoped RealInnerProductSpace

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-! ## Simple Calibrated Forms -/

/-- The strongly positive cone K_p(x) at a point x is the convex cone hull
of simple calibrated forms. -/
def stronglyPositiveCone (p : ℕ) (x : X) : Set (SmoothForm n X (2 * p)) :=
  (ConvexCone.hull ℝ (simpleCalibratedForms p x)).carrier

/-- The strongly positive cone is convex. -/
theorem stronglyPositiveCone_convex (p : ℕ) (x : X) :
    Convex ℝ (stronglyPositiveCone p x) :=
  (ConvexCone.hull ℝ (simpleCalibratedForms p x)).convex

/-- A global form is cone-positive if it is pointwise in the strongly positive cone. -/
def isConePositive {p : ℕ} (α : SmoothForm n X (2 * p)) : Prop :=
  ∀ x, α ∈ stronglyPositiveCone p x

/-! ## Kähler Power -/

/-- The p-th power of the Kähler form ω^p at a point x. -/
def omegaPow_point (p : ℕ) (_x : X) : SmoothForm n X (2 * p) :=
  omegaPow n X p

/-- **Axiom: Wirtinger Inequality** (Pointwise):
The pairing of ω^p with any simple calibrated form is exactly 1. -/
axiom wirtinger_pairing (p : ℕ) (x : X) (ξ : SmoothForm n X (2 * p))
    (hξ : ξ ∈ simpleCalibratedForms p x) :
    pointwiseInner (omegaPow_point p x) ξ x = 1

/-- **Theorem: ω^p is in the interior of K_p(x)**. -/
theorem omegaPow_in_interior (p : ℕ) (x : X) :
    (omegaPow_point p x) ∈ interior (stronglyPositiveCone p x) := by
  -- Follows from pairing positively with all generators.
  -- Axiomatized for now.
  sorry

/-- **Uniform Interior Radius Theorem**:
There exists a uniform interior radius r > 0 such that B(ω^p(x), r) ⊆ K_p(x) for all x ∈ X. -/
theorem exists_uniform_interior_radius [CompactSpace X] [Nonempty X] (p : ℕ) :
    ∃ r : ℝ, r > 0 ∧ ∀ x : X, ball (omegaPow_point p x) r ⊆ stronglyPositiveCone p x := by
  -- Local existence
  have h_local : ∀ x, ∃ r > 0, ball (omegaPow_point p x) r ⊆ stronglyPositiveCone p x := by
    intro x
    have h_int := omegaPow_in_interior p x
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h_int
    exact h_int
  -- Radius function
  let f : X → ℝ := fun x => sSup { r | r > 0 ∧ ball (omegaPow_point p x) r ⊆ stronglyPositiveCone p x }
  -- Axiom: continuity of the radius function
  have h_cont : Continuous f := sorry
  have h_pos : ∀ x, f x > 0 := by
    intro x; obtain ⟨r, hr_pos, hr_ball⟩ := h_local x
    apply lt_of_lt_of_le hr_pos; apply le_csSup _ ⟨hr_pos, hr_ball⟩
    use 1; sorry
  obtain ⟨r, hr_pos, hr_le⟩ := compact_pos_has_pos_inf f h_cont h_pos
  use r, hr_pos
  intro x; intro y hy
  -- Inclusion
  sorry

/-! ## Carathéodory Decomposition -/

/-- **Cone Hull Characterization**: Elements of the cone hull are finite non-negative
linear combinations of generators. -/
theorem conic_hull_mem_finite_sum {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (S : Set E) (β : E) (hβ : β ∈ ConvexCone.hull ℝ S) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (ξ : Fin N → E),
      (∀ i, c i ≥ 0) ∧ (∀ i, ξ i ∈ S) ∧ β = ∑ i, c i • ξ i := by
  induction hβ using ConvexCone.hull_induction ℝ S with
  | mem x hx =>
    use 1, fun _ => 1, fun _ => x
    simp [hx]
  | zero =>
    use 0, fun i => i.elim, fun i => i.elim
    simp
  | add x y _ _ hx hy =>
    obtain ⟨Nx, cx, ξx, hcx, hξx, rfl⟩ := hx
    obtain ⟨Ny, cy, ξy, hcy, hξy, rfl⟩ := hy
    use Nx + Ny, Fin.addCases cx cy, Fin.addCases ξx ξy
    constructor
    · intro i; induction i using Fin.addCases with | left i => exact hcx i | right i => exact hcy i
    · constructor
      · intro i; induction i using Fin.addCases with | left i => exact hξx i | right i => exact hξy i
      · rw [Finset.sum_addCases]
  | smul c x _ hc hx =>
    obtain ⟨N, c', ξ, hc', hξ, rfl⟩ := hx
    use N, fun i => c * c' i, ξ
    constructor
    · intro i; exact mul_nonneg hc (hc' i)
    · constructor
      · exact hξ
      · rw [Finset.smul_sum]; simp_rw [smul_smul]

/-- **Carathéodory Decomposition Theorem**: Any element of K_p(x) can be written as
    a finite conic combination of simple calibrated forms. -/
theorem caratheodory_decomposition (p : ℕ) (x : X)
    (β : SmoothForm n X (2 * p)) (hβ : β ∈ stronglyPositiveCone p x) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (ξ : Fin N → SmoothForm n X (2 * p)),
      (∀ i, c i ≥ 0) ∧ (∀ i, ξ i ∈ simpleCalibratedForms p x) ∧
      β = ∑ i, c i • ξ i :=
  conic_hull_mem_finite_sum (simpleCalibratedForms p x) β hβ

/-- **Helper**: On a compact space, a continuous positive function has a positive infimum. -/
theorem compact_pos_has_pos_inf {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [Nonempty Y] (f : Y → ℝ) (hf_cont : Continuous f) (hf_pos : ∀ y, f y > 0) :
    ∃ r : ℝ, r > 0 ∧ ∀ y, f y ≥ r := by
  have hc : IsCompact (univ : Set Y) := isCompact_univ
  have hne : (univ : Set Y).Nonempty := univ_nonempty
  obtain ⟨y₀, _, hy₀⟩ := hc.exists_isMinOn hne hf_cont.continuousOn
  use f y₀, hf_pos y₀
  intro y; exact hy₀ (mem_univ y)

end
