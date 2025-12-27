import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Hodge.Analytic.Norms
import Hodge.Analytic.Grassmannian
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Track C.3: Strongly Positive Cone
-/

noncomputable section

open Classical Metric

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-! ## Simple Calibrated Forms -/

/-- The strongly positive cone K_p(x) at a point x is the convex cone hull
of simple calibrated forms.
Reference: [Harvey-Lawson, 1982]. -/
def stronglyPositiveCone (p : ℕ) (x : X) : Set (SmoothForm n X (2 * p)) :=
  (ConvexCone.hull ℝ (simpleCalibratedForms p x) : Set _)

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
  omegaPow p

/-- **Wirtinger Inequality** (Pointwise):
The pairing of ω^p with any simple calibrated form is exactly 1.
Reference: [Harvey-Lawson, 1982, p. 17]. -/
theorem wirtinger_pairing (p : ℕ) (x : X) (ξ : SmoothForm n X (2 * p))
    (_hξ : ξ ∈ simpleCalibratedForms p x) :
    pointwiseInner (omegaPow_point p x) ξ x = 1 := by
  -- 1. Choose an orthonormal basis {e_1, Je_1, ..., e_p, Je_p} for the complex subspace V.
  -- 2. The volume form ξ of V satisfies ξ(e_1, Je_1, ..., e_p, Je_p) = 1.
  -- 3. The Kähler power ω^p satisfies (ω^p/p!)(e_1, Je_1, ..., e_p, Je_p) = 1.
  -- 4. Thus the inner product is 1.
  sorry

/-- A point lies in the interior of a convex cone if it pairs strictly positively
with all non-zero elements of the dual cone. -/
theorem ConvexCone.mem_interior_of_pairing_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (C : ConvexCone ℝ E) (x : E) :
    (∀ y ∈ C.dual, y ≠ 0 → inner y x > 0) → x ∈ interior (C : Set E) := by
  -- 1. In finite dimensions, a closed convex cone is equal to its double dual.
  -- 2. The interior of C consists of vectors that are strictly positive on the dual cone (excluding 0).
  -- 3. This is a consequence of the hyperplane separation theorem.
  sorry

/-- **CRITICAL THEOREM**: ω^p is in the interior of K_p(x). -/
theorem omegaPow_in_interior (p : ℕ) (x : X) :
    (omegaPow_point (n := n) (X := X) p x) ∈ interior (stronglyPositiveCone (n := n) (X := X) p x) := by
  -- 1. Simple calibrated forms generate the strongly positive cone K_p(x).
  -- 2. By the Wirtinger inequality, ω^p pairs strictly positively with all simple calibrated forms.
  -- 3. In finite dimensions, this implies ω^p lies in the interior of the cone.
  sorry

/-! ## Uniform Interior Radius -/

/-- There exists a uniform interior radius r > 0 such that
B(ω^p(x), r) ⊆ K_p(x) for all x ∈ X. -/
theorem exists_uniform_interior_radius [CompactSpace X] (p : ℕ) :
    ∃ r : ℝ, r > 0 ∧ ∀ x : X, ball (omegaPow_point (n := n) (X := X) p x) r ⊆ stronglyPositiveCone (n := n) (X := X) p x := by
  -- 1. For each x, ω^p(x) is in the interior of the strongly positive cone (Theorem C.3.4).
  -- 2. Thus there exists a radius r(x) > 0 such that ball(ω^p(x), r(x)) ⊆ K_p(x).
  -- 3. Since ω^p varies smoothly and K_p is a continuous family of cones,
  --    the function x ↦ sup { r | ball(ω^p(x), r) ⊆ K_p(x) } is continuous.
  -- 4. By the Extreme Value Theorem, this function attains its minimum on compact X.
  -- 5. Since the function is positive everywhere, its minimum r is positive.
  sorry

/-! ## Carathéodory Decomposition -/

/-- Any element of K_p(x) can be written as a finite convex combination
of simple calibrated forms.
Reference: [Carathéodory, 1907]. -/
theorem caratheodory_decomposition (p : ℕ) (x : X)
    (β : SmoothForm n X (2 * p)) (_hβ : β ∈ stronglyPositiveCone p x) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (ξ : Fin N → SmoothForm n X (2 * p)),
      (∀ i, c i ≥ 0) ∧ (∀ i, ξ i ∈ simpleCalibratedForms p x) ∧
      β = ∑ i, c i • ξ i := by
  -- 1. The strongly positive cone is the convex cone hull of simple calibrated forms.
  -- 2. By Carathéodory's theorem, any point in the convex hull of a set S can be
  --    represented as a combination of at most dim(E)+1 points.
  sorry

end
