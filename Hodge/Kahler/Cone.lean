/-!
# Track C.3: Strongly Positive Cone
-/

import Hodge.Kahler.Manifolds
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.NormedSpace.Basic

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [SmoothManifoldWithCorners 𝓒(Complex, n) X] [K : KahlerManifold n X]

/-! ## Form Spaces -/

import Hodge.Kahler.TypeDecomposition

/-- The vector space of real (p,p)-forms at a point x. -/
def PPFormSpace (n : ℕ) (X : Type*) (p : ℕ) (x : X)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
    [SmoothManifoldWithCorners 𝓒(Complex, n) X] :=
  { α : AlternatingMap ℝ (TangentSpace 𝓒(Complex, n) x) ℝ (Fin (2 * p)) //
    ∀ v, α (fun i => Complex.I • v i) = α v }

instance (n : ℕ) (X : Type*) (p : ℕ) (x : X)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
    [SmoothManifoldWithCorners 𝓒(Complex, n) X] :
    AddCommGroup (PPFormSpace n X p x) :=
  Subtype.addCommGroup (fun α => ∀ v, α (fun i => Complex.I • v i) = α v)

instance (n : ℕ) (X : Type*) (p : ℕ) (x : X)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
    [SmoothManifoldWithCorners 𝓒(Complex, n) X] :
    Module ℝ (PPFormSpace n X p x) :=
  Subtype.module ℝ (fun α => ∀ v, α (fun i => Complex.I • v i) = α v)

instance (n : ℕ) (X : Type*) (p : ℕ) (x : X)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
    [SmoothManifoldWithCorners 𝓒(Complex, n) X] :
    FiniteDimensional ℝ (PPFormSpace n X p x) :=
  FiniteDimensional.of_injective (Submodule.subtype _) Subtype.coe_injective

instance (n : ℕ) (X : Type*) (p : ℕ) (x : X)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
    [SmoothManifoldWithCorners 𝓒(Complex, n) X] :
    TopologicalSpace (PPFormSpace n X p x) :=
  inferInstance

/-! ## Simple Calibrated Forms -/

/-- The calibrated Grassmannian G_p(x): the set of complex p-planes in T_x X. -/
def CalibratedGrassmannian (p : ℕ) (x : X) : Set (Submodule Complex (TangentSpace 𝓒(Complex, n) x)) :=
  { V | FiniteDimensional.finrank Complex V = p }

/-- A simple calibrated (p,p)-form at x is the unit volume form of a complex p-plane. -/
def SimpleCalibratedForm (p : ℕ) (x : X)
    (V : CalibratedGrassmannian p x) : PPFormSpace n X p x :=
  ⟨(simpleCalibratedForm p x V.1) x, (isPPForm_simple p x V.1 V.2)⟩

/-- The set of all simple calibrated forms at x. -/
def simpleCalibratedForms (p : ℕ) (x : X) : Set (PPFormSpace n X p x) :=
  { ξ | ∃ V : CalibratedGrassmannian p x, ξ = SimpleCalibratedForm p x V }

/-! ## Strongly Positive Cone -/

/-- The strongly positive cone K_p(x) at a point x. -/
def stronglyPositiveCone (p : ℕ) (x : X) : ConvexCone ℝ (PPFormSpace n X p x) :=
  ConvexCone.convexConeHull ℝ (simpleCalibratedForms p x)

/-- The strongly positive cone is convex. -/
theorem stronglyPositiveCone_convex (p : ℕ) (x : X) :
    Convex ℝ (stronglyPositiveCone p x : Set (PPFormSpace n X p x)) :=
  (stronglyPositiveCone p x).convex

/-- A global form is cone-positive if it is pointwise in the strongly positive cone. -/
def isConePositive {p : ℕ} (α : SmoothForm n X (2 * p)) : Prop :=
  ∀ x, (α x) ∈ (stronglyPositiveCone p x : Set (PPFormSpace n X p x))

/-! ## Kähler Power -/

/-- The p-th power of the Kähler form ω^p at a point x. -/
def omegaPow_point (p : ℕ) (x : X) : PPFormSpace n X p x :=
  ⟨(omegaPow p) x, (omega_pow_is_p_p p) x⟩

/-- **Wirtinger Inequality** (Pointwise):
The pairing of ω^p with any simple calibrated form is exactly 1.
⟨ω^p, ξ⟩ = 1.
Reference: [Harvey-Lawson, 1982, p. 17]. -/
theorem wirtinger_pairing (p : ℕ) (x : X) (V : CalibratedGrassmannian p x) :
    pointwiseInner (omegaPow_point p x).val (SimpleCalibratedForm p x V).val x = 1 := by
  -- 1. Let {e_1, Je_1, ..., e_p, Je_p} be a unitary basis for the oriented real subspace V.
  -- 2. The normalized simple form ξ_V satisfies ξ_V(e_1, ..., Je_p) = 1.
  -- 3. The Kähler power ω^p satisfies ω^p(e_1, ..., Je_p) = p!.
  -- 4. By definition, SimpleCalibratedForm is (1/p!) ω^p|_V.
  -- 5. Thus the pointwise inner product is 1.
  sorry

/-- A point lies in the interior of a convex cone if it pairs strictly positively
with all non-zero elements of the dual cone.
Reference: [Boyd-Vandenberghe, 2004, Section 2.6]. -/
theorem ConvexCone.mem_interior_of_pairing_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (C : ConvexCone ℝ E) (v : E)
    (h_pos : ∀ ξ ∈ PointedCone.dual (InnerProductSpace.toDual ℝ E) (C : Set E), ξ ≠ 0 → inner ξ v > (0 : ℝ)) :
    v ∈ interior (C : Set E) := by
  -- 1. In finite dimensions, a closed convex cone is equal to its double dual.
  -- 2. The interior of C consists of vectors that are strictly positive on the dual cone (excluding 0).
  -- 3. This is a consequence of the hyperplane separation theorem.
  sorry

/-- **CRITICAL THEOREM**: ω^p is in the interior of K_p(x). -/
theorem omegaPow_in_interior (p : ℕ) (x : X) :
    (omegaPow_point p x) ∈ interior (stronglyPositiveCone p x : Set (PPFormSpace n X p x)) := by
  -- 1. Use the dual pairing characterization of the interior.
  apply (stronglyPositiveCone p x).mem_interior_of_pairing_pos
  · intro ξ hξ h_nz
    -- 2. Any ξ in the dual cone pairs non-negatively with all simple calibrated forms.
    -- 3. Since the simple calibrated forms generate the cone K_p(x), and ω^p
    --    is strictly positive on the generators (Wirtinger), it must be strictly
    --    positive on any non-zero dual vector.
    sorry

/-! ## Uniform Interior Radius -/

/-- There exists a uniform interior radius r > 0 such that
B(ω^p(x), r) ⊆ K_p(x) for all x ∈ X.

This follows from the compactness of X and the continuity of the Kähler power.
Reference: [Voisin, 2002]. -/
theorem exists_uniform_interior_radius [CompactSpace X] (p : ℕ) :
    ∃ r : ℝ, r > 0 ∧ ∀ x, Metric.ball (omegaPow_point p x).val r ⊆ (stronglyPositiveCone p x : Set (PPFormSpace n X p x)) := by
  -- 1. For each x, ω^p(x) is in the interior of the strongly positive cone.
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
    (β : PPFormSpace n X p x) (hβ : β ∈ (stronglyPositiveCone p x : Set (PPFormSpace n X p x))) :
    ∃ (N : ℕ) (θ : Fin N → ℝ) (ξ : Fin N → PPFormSpace n X p x),
      (∀ i, θ i ≥ 0) ∧
      (∀ i, ξ i ∈ simpleCalibratedForms p x) ∧
      β = ∑ i, θ i • (ξ i) := by
  -- 1. The strongly positive cone is the convex cone hull of simple calibrated forms.
  -- 2. By Carathéodory's theorem, any point in the convex hull of a set S can be
  --    represented as a combination of at most dim(E)+1 points.
  sorry

end
