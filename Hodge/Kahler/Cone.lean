/-!
# Track C.3: Strongly Positive Cone

This file defines the strongly positive cone K_p of calibrated (p,p)-forms
and proves key properties including that ω^p lies in its interior.

## Contents
- Simple calibrated forms (unit volume forms of p-planes)
- Strongly positive cone as convex hull
- ω^p in interior of cone
- Carathéodory decomposition

## Status
- [ ] Define simple calibrated forms
- [ ] Define strongly positive cone as convexHull
- [ ] Prove cone is a proper convex cone
- [ ] **CRITICAL**: Prove omega_pow_in_interior
- [ ] Prove uniform interior radius exists
- [ ] Derive Carathéodory decomposition
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

/-- The vector space of real (p,p)-forms at a point x.
A form is of type (p,p) if it is invariant under the complex structure J. -/
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

/-- The calibrated Grassmannian G_p(x): the set of complex p-planes in T_x X.
Each such plane V defines a unit volume form. -/
def CalibratedGrassmannian (p : ℕ) (x : X) : Set (Submodule Complex (TangentSpace 𝓒(Complex, n) x)) :=
  { V | FiniteDimensional.finrank Complex V = p }

/-- A simple calibrated (p,p)-form at x is the unit volume form of a complex p-plane.
These are the "extremal" elements of the cone K_p(x). -/
def SimpleCalibratedForm (p : ℕ) (x : X)
    (V : CalibratedGrassmannian p x) : PPFormSpace n X p x :=
  ⟨(simpleCalibratedForm p x V.1) x, (isPPForm_simple p x V.1 V.2)⟩

/-- The set of all simple calibrated forms at x. -/
def simpleCalibratedForms (p : ℕ) (x : X) : Set (PPFormSpace n X p x) :=
  { ξ | ∃ V : CalibratedGrassmannian p x, ξ = SimpleCalibratedForm p x V }

/-! ## Strongly Positive Cone -/

/-- The strongly positive cone K_p(x) at a point x.
Defined as the convex cone hull of the simple calibrated forms. -/
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

/-- The p-th power of the Kähler form ω^p at a point x.
This is a (p,p)-form defined by wedging ω with itself p times. -/
def omegaPow (p : ℕ) (x : X) : PPFormSpace n X p x :=
  ⟨(omegaPow' p) x, (omega_pow_is_p_p p) x⟩

/-- **Wirtinger Inequality** (Pointwise):
The pairing of ω^p with any simple calibrated form is exactly 1.
⟨ω^p, ξ⟩ = 1.
Reference: [Harvey-Lawson, 1982]. -/
theorem wirtinger_pairing (p : ℕ) (x : X) (V : CalibratedGrassmannian p x) :
    pointwiseInner (omegaPow p x).val (SimpleCalibratedForm p x V).val x = 1 := by
  -- Let V be a complex p-plane. Let {e_1, Je_1, ..., e_p, Je_p} be a unitary basis for V.
  -- The Kähler form ω is given by Σ dz_j ∧ d\bar{z}_j.
  -- Then ω^p(e_1, Je_1, ..., e_p, Je_p) = p!.
  -- The simple calibrated form ξ_V is (1/p!) ω^p|_V.
  -- This identity follows from the algebraic properties of the Kähler form.
  sorry

/-- A point lies in the interior of a convex cone if it pairs strictly positively
with all non-zero elements of the dual cone.
This is a standard result in finite-dimensional convex analysis. -/
theorem ConvexCone.mem_interior_of_pairing_pos {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (C : ConvexCone ℝ E) (v : E)
    (h_pos : ∀ ξ ∈ PointedCone.dual (InnerProductSpace.toDual ℝ E) (C : Set E), ξ ≠ 0 → inner ξ v > (0 : ℝ)) :
    v ∈ interior (C : Set E) := by
  -- Proof by contradiction: if v is not in the interior, there exists a supporting hyperplane.
  -- This hyperplane defines a non-zero dual vector whose pairing with v is zero.
  -- This contradicts the hypothesis h_pos.
  sorry

/-- **CRITICAL THEOREM**: ω^p is in the interior of K_p(x). -/
theorem omegaPow_in_interior (p : ℕ) (x : X) :
    (omegaPow p x) ∈ interior (stronglyPositiveCone p x : Set (PPFormSpace n X p x)) := by
  -- 1. Simple calibrated forms generate the cone K_p(x).
  -- 2. By Wirtinger inequality, ω^p pairs strictly positively with all simple calibrated forms.
  -- 3. In finite dimensions, if a vector pairs strictly positively with all non-zero
  --    elements of the dual cone, it lies in the interior.
  apply (stronglyPositiveCone p x).mem_interior_of_pairing_pos
  · -- ω^p pairs strictly positively with dual vectors
    intro ξ hξ h_nz
    -- ξ is in the dual cone, so it pairs non-negatively with all simple calibrated forms.
    -- Since ω^p is a strictly positive sum of these (spiritually), its pairing with ξ is positive.
    sorry

/-! ## Uniform Interior Radius -/

/-- There exists a uniform interior radius r > 0 such that
B(ω^p(x), r) ⊆ K_p(x) for all x ∈ X.

This follows from the compactness of X and the continuity of the Kähler power.
Reference: [Voisin, 2002]. -/
theorem exists_uniform_interior_radius [CompactSpace X] (p : ℕ) :
    ∃ r : ℝ, r > 0 ∧ ∀ x, Metric.ball (omegaPow p x).val r ⊆ (stronglyPositiveCone p x : Set (PPFormSpace n X p x)) := by
  -- Let f(x) be the supremum of radii r such that ball(ω^p(x), r) ⊆ K_p(x).
  -- This function is continuous because the Kähler form and the cone vary smoothly.
  -- Since X is compact, f attains its minimum r_min on X.
  -- Since ω^p(x) is in the interior for all x, r_min > 0.
  have h_compact : IsCompact (Set.univ : Set X) := isCompact_univ
  let f : X → ℝ := fun x => sSup { r | Metric.ball (omegaPow p x).val r ⊆ (stronglyPositiveCone p x : Set (PPFormSpace n X p x)) }
  
  have h_f_pos : ∀ x, f x > 0 := by
    intro x
    obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_interior.mem_nhds (omegaPow_in_interior p x)
    apply lt_of_lt_of_le hr_pos
    apply le_sSup
    use r, hr_ball

  -- f is continuous because the Kähler power and the cone vary smoothly with x.
  -- By the Extreme Value Theorem on compact X, f attains its minimum at some x_min.
  -- Since f(x) > 0 for all x, the minimum is positive.
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
  -- stronglyPositiveCone is the convex cone hull of simpleCalibratedForms.
  -- This is equivalent to the convex hull of the union of the rays.
  -- By Carathéodory's theorem, any point in the convex hull of a set S in ℝ^d
  -- is a convex combination of at most d+1 points from S.
  -- Here S is the set of rays generated by simple calibrated forms.
  sorry

end
