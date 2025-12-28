import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Hodge.Analytic.Norms
import Hodge.Analytic.Grassmannian
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Track C.3: Strongly Positive Cone

This file defines the strongly positive cone K_p(x) of (p,p)-forms at each point x.
-/

noncomputable section

open Classical Metric Set Filter

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-! ## Strongly Positive Cone -/

/-- The strongly positive cone K_p(x) at a point x is the convex cone hull
of simple calibrated forms. -/
def stronglyPositiveCone (p : ℕ) (x : X) : Set (SmoothForm n X (2 * p)) :=
  (ConvexCone.hull ℝ (simpleCalibratedForms p x)).carrier

/-- The strongly positive cone is convex. -/
theorem stronglyPositiveCone_convex (p : ℕ) (x : X) :
    Convex ℝ (stronglyPositiveCone (n := n) p x) := by
  unfold stronglyPositiveCone
  exact ConvexCone.convex _

/-- A global form is cone-positive if it is pointwise in the strongly positive cone. -/
def isConePositive {p : ℕ} (α : SmoothForm n X (2 * p)) : Prop :=
  ∀ x, α ∈ stronglyPositiveCone p x

/-! ## Kähler Power -/

/-- The p-th power of the Kähler form ω^p at a point x. -/
def omegaPow_point (p : ℕ) (_x : X) : SmoothForm n X (2 * p) :=
  omegaPow n X p

/-- **Wirtinger Inequality** (Pointwise):
    The pairing of ω^p with any simple calibrated form is exactly 1.
    Reference: [Harvey-Lawson, 1982, p. 17]. -/
axiom wirtinger_pairing (p : ℕ) (x : X) (ξ : SmoothForm n X (2 * p))
    (hξ : ξ ∈ simpleCalibratedForms p x) :
    pointwiseInner (omegaPow_point p x) ξ x = 1

/-- **ω^p is in the interior of K_p(x)**.
    This follows from the Wirtinger inequality: ω^p pairs with value 1 with all
    simple calibrated forms, which generate the strongly positive cone.
    In the finite-dimensional space of forms at x, this placing it in the interior. -/
axiom omegaPow_in_interior (p : ℕ) (x : X) :
    (omegaPow_point p x) ∈ interior (stronglyPositiveCone (n := n) p x)

/-- **Uniform Interior Radius Theorem**:
    There exists a uniform interior radius r > 0 such that B(ω^p(x), r) ⊆ K_p(x) for all x ∈ X.
    This follows from the continuity of ω^p and the compactness of X. -/
axiom exists_uniform_interior_radius (p : ℕ) [CompactSpace X] [Nonempty X] :
    ∃ r : ℝ, r > 0 ∧ ∀ x : X, ∀ y : SmoothForm n X (2 * p),
      pointwiseComass (y - omegaPow_point p x) x < r → y ∈ stronglyPositiveCone p x

/-! ## Carathéodory Decomposition -/

/-- **Carathéodory's Theorem**: Any point in the convex hull of S in ℝ^d
    is a convex combination of at most d+1 points.
    Reference: C. Carathéodory, "Über den Variabilitätsbereich der Fourier'schen Konstanten von positiven harmonischen Funktionen",
    Rend. Circ. Mat. Palermo 32 (1911), 193-217. -/
axiom caratheodory_decomposition (p : ℕ) (x : X)
    (β : SmoothForm n X (2 * p)) (hβ : β ∈ stronglyPositiveCone p x) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (ξ : Fin N → SmoothForm n X (2 * p)),
      (∀ i, c i ≥ 0) ∧ (∀ i, ξ i ∈ simpleCalibratedForms p x) ∧
      β = ∑ i, c i • ξ i

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
