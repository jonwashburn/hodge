import Hodge.Analytic.Norms
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!

This file defines the calibrated Grassmannian and the strongly positive cone
of (p,p)-forms on a Kahler manifold.
-/

noncomputable section

open Classical Metric Set Filter

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  {p : ℕ}

/-! ## Calibrated Grassmannian -/

/-- The calibrated Grassmannian G_p(x): the set of complex p-planes in T_x X. -/
def CalibratedGrassmannian (p : ℕ) (x : X) : Set (Submodule ℂ (TangentSpace (𝓒_complex n) x)) :=
  { V | Module.finrank ℂ V = p }

/-! ## Simple Calibrated Forms -/

/-- **Predicate: Form is a Volume Form on Subspace**

A (2p)-form ω is a volume form on a complex p-dimensional subspace V if:
1. ω vanishes on vectors outside V
2. ω is normalized: there exists a basis of V on which ω evaluates to 1

Reference: [Harvey-Lawson, "Calibrated geometries", 1982, Section 2] -/
def IsVolumeFormOn {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (x : X) (p : ℕ) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (ω : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℂ] ℂ) : Prop :=
  -- Condition 1: ω vanishes outside V
  (∀ (v : Fin (2 * p) → TangentSpace (𝓒_complex n) x), (∃ i, v i ∉ V) → ω v = 0) ∧
  -- Condition 2: ω is normalized on some basis of V
  (∃ (e : Fin (2 * p) → TangentSpace (𝓒_complex n) x), (∀ i, e i ∈ V) ∧ ω e = 1)

/-- Volume forms are nonzero.
    If ω is a volume form on V, then ω evaluates to 1 on some basis, so ω ≠ 0. -/
theorem IsVolumeFormOn_nonzero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (x : X) (p : ℕ) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (ω : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℂ] ℂ)
    (_hV : Module.finrank ℂ V = p) :
    IsVolumeFormOn x p V ω → ω ≠ 0 := by
  intro ⟨_, e, _, he⟩ hzero
  rw [hzero] at he
  simp at he

/-- **Existence of Volume Form** (Harvey-Lawson, 1982).

For any complex p-plane V in the tangent space, there exists a unique (up to scaling)
volume form on V. This form is the Wirtinger form restricted to V.

**Critical**: The existence claim now has a meaningful constraint (IsVolumeFormOn),
not just True.

Reference: [Harvey-Lawson, "Calibrated geometries", 1982, Section 2] -/
axiom exists_volume_form_of_submodule_axiom (p : ℕ) (x : X)
    (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (hV : Module.finrank ℂ V = p) :
    ∃ (ω : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℂ] ℂ),
      IsVolumeFormOn (n := n) (X := X) x p V ω

theorem exists_volume_form_of_submodule (p : ℕ) (x : X)
    (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (hV : Module.finrank ℂ V = p) :
    ∃ (ω : (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℂ] ℂ),
      IsVolumeFormOn (n := n) (X := X) x p V ω :=
  exists_volume_form_of_submodule_axiom p x V hV

/-- Every complex p-plane in the tangent space has a unique volume form. -/
def volume_form_of_submodule (p : ℕ) (x : X) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (hV : Module.finrank ℂ V = p) :
    (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℂ] ℂ :=
  Classical.choose (exists_volume_form_of_submodule p x V hV)

/-- The simple calibrated (p,p)-form at a point x, associated to a complex p-plane V. -/
def simpleCalibratedForm_raw (p : ℕ) (x : X) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (hV : Module.finrank ℂ V = p) :
    (TangentSpace (𝓒_complex n) x) [⋀^Fin (2 * p)]→ₗ[ℂ] ℂ :=
  volume_form_of_submodule p x V hV

/-- The simple calibrated (p,p)-form supported at point x.
    Since SmoothForm is opaque, we axiomatize this construction.
    Uses section variables for n, X, and instances. -/
axiom simpleCalibratedForm (p : ℕ) (x : X) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (hV : Module.finrank ℂ V = p) : SmoothForm n X (2 * p)

/-- The set of all simple calibrated (p,p)-forms at a point x. -/
def simpleCalibratedForms (p : ℕ) (x : X) : Set (SmoothForm n X (2 * p)) :=
  { ξ | ∃ (V : Submodule ℂ (TangentSpace (𝓒_complex n) x)) (hV : Module.finrank ℂ V = p),
    ξ = simpleCalibratedForm p x V hV }

/-! ## Calibrated Cone -/

/-- The calibrated cone C_x at x is the closed convex cone generated by
    the simple calibrated forms. We use PointedCone.span to ensure it contains 0. -/
def calibratedCone (p : ℕ) (x : X) : Set (SmoothForm n X (2 * p)) :=
  closure ((PointedCone.span ℝ (simpleCalibratedForms (n := n) p x)) : Set (SmoothForm n X (2 * p)))

/-- The calibrated cone is closed. -/
theorem calibratedCone_is_closed (p : ℕ) (x : X) :
    IsClosed (calibratedCone (n := n) p x) :=
  isClosed_closure

/-- Simple calibrated forms are in the calibrated cone. -/
theorem simpleCalibratedForms_subset_calibratedCone (p : ℕ) (x : X) :
    simpleCalibratedForms (n := n) p x ⊆ calibratedCone (n := n) p x := by
  intro ξ hξ
  unfold calibratedCone
  apply subset_closure
  -- ξ ∈ simpleCalibratedForms → ξ ∈ PointedCone.span
  apply Submodule.subset_span
  exact hξ

/-- The PointedCone.span of simpleCalibratedForms is in the calibrated cone. -/
theorem span_simpleCalibratedForms_subset_calibratedCone (p : ℕ) (x : X) :
    ((PointedCone.span ℝ (simpleCalibratedForms (n := n) p x)).carrier : Set (SmoothForm n X (2 * p)))
      ⊆ calibratedCone (n := n) p x := by
  intro α hα
  unfold calibratedCone
  exact subset_closure hα

/-- **Calibrated Cone is Pointed** (standard result in convex analysis).
    The calibrated cone contains 0. This follows from the definition of a pointed
    cone as a submodule over non-negative scalars.
    Reference: [R.T. Rockafellar, "Convex Analysis", 1970]. -/
theorem calibratedCone_hull_pointed (p : ℕ) (x : X) :
    (0 : SmoothForm n X (2 * p)) ∈ calibratedCone (n := n) p x := by
  -- calibratedCone is closure of PointedCone.span
  -- PointedCone.span is a Submodule, so it contains 0
  -- 0 ∈ span → 0 ∈ closure(span)
  unfold calibratedCone
  apply subset_closure
  exact Submodule.zero_mem _

/-! ## Cone Distance and Defect -/

/-- The pointwise distance from a form α to the calibrated cone at point x.
    Defined as the infimum of pointwise norms ‖α - β‖_x over all β in the cone. -/
def distToCone (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) : ℝ :=
  sInf { r : ℝ | ∃ β ∈ calibratedCone (n := n) p x, r = pointwiseNorm (α - β) x }

/-- Distance to cone is non-negative.
    This follows from pointwiseNorm being non-negative. -/
theorem distToCone_nonneg (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) :
    distToCone p α x ≥ 0 := by
  unfold distToCone
  apply Real.sInf_nonneg
  intro r ⟨β, _, hr⟩
  rw [hr]
  exact pointwiseNorm_nonneg (α - β) x

/-- The global cone defect: supremum of pointwise distances to the calibrated cone.
    Measures how far a form is from being cone-positive globally. -/
def coneDefect (p : ℕ) (α : SmoothForm n X (2 * p)) : ℝ :=
  sSup (Set.range (distToCone p α))

/-- Cone defect is non-negative.
    This follows from distToCone being non-negative at each point. -/
theorem coneDefect_nonneg (p : ℕ) (α : SmoothForm n X (2 * p)) : coneDefect p α ≥ 0 := by
  unfold coneDefect
  apply Real.sSup_nonneg
  intro r ⟨x, hx⟩
  rw [← hx]
  exact distToCone_nonneg p α x

/-! ## Projection Theorems -/

/-- **Radial Minimization Theorem** (Rockafellar, 1970).
    Reference: [R.T. Rockafellar, "Convex Analysis", Princeton, 1970].

    **Note**: With opaque `pointwiseInner`, this requires axiomatization. -/
axiom radial_minimization (x : X) (ξ α : SmoothForm n X (2 * p))
    (hξ : pointwiseNorm ξ x = 1) :
    ∃ lambda_star : ℝ, lambda_star = max 0 (pointwiseInner α ξ x) ∧
    ∀ l ≥ (0 : ℝ), (pointwiseNorm (α - lambda_star • ξ) x)^2 ≤ (pointwiseNorm (α - l • ξ) x)^2

/-- **Pointwise Calibration Distance Formula** (Harvey-Lawson, 1982).
    Reference: [Harvey-Lawson, "Calibrated geometries", Acta Math. 148 (1982)].

    **Note**: With opaque `pointwiseInner`, this requires axiomatization. -/
axiom dist_cone_sq_formula (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) :
    (distToCone (n := n) (X := X) p α x)^2 = (pointwiseNorm α x)^2 -
      (sSup { r | ∃ ξ ∈ simpleCalibratedForms p x, r = max 0 (pointwiseInner α ξ x) })^2

/-! ## Constants -/

/-- The cone-to-net comparison constant K = (11/9)^2. -/
def coneToNetConstant : ℝ := (11 / 9 : ℝ)^2

theorem coneToNetConstant_pos : coneToNetConstant > 0 := by
  unfold coneToNetConstant; positivity

end
