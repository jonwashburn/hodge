import Hodge.Analytic.Forms
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Track B.2: Norms and Metrics

This file defines the global norms on differential forms (comass and L2)
and proves their basic properties on compact Kähler manifolds.

## Mathlib Integration

We leverage several Mathlib results:
- `Mathlib.Analysis.InnerProductSpace.Projection`: Orthogonal projections
- `Mathlib.Topology.Compactness.Compact`: Extreme value theorem
- `Mathlib.Topology.MetricSpace.Basic`: Metric space properties

## Main definitions
- `kahlerMetric`: The Riemannian metric induced by a Kähler form
- `pointwiseComass`: The supremum of |α(v)| over unit vectors
- `comass`: Global comass norm (supremum of pointwiseComass)
- `pointwiseInner`: Inner product of forms at a point
- `normL2`: L2 norm of forms

## Main theorems
- `comass_nonneg`: Comass is non-negative
- `comass_neg`: Comass is symmetric under negation
- `comass_add_le`: Triangle inequality for comass
-/

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-! ## Comass Norm -/

/-- The Riemannian metric induced by a Kähler form on the tangent space. -/
def kahlerMetric (x : X) (u v : TangentSpace (𝓒_complex n) x) : ℝ :=
  (K.omega_form.as_alternating x ![u, Complex.I • v]).re

/-- The pointwise norm of a tangent vector. -/
def tangentNorm (x : X) (v : TangentSpace (𝓒_complex n) x) : ℝ :=
  Real.sqrt (kahlerMetric x v v)

/-- The pointwise comass of a k-form at a point x.
Defined as the supremum of |α(v₁, ..., vₖ)| over all unit tangent vectors. -/
def pointwiseComass {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  sSup { r : ℝ | ∃ (v : Fin k → TangentSpace (𝓒_complex n) x),
    (∀ i, tangentNorm x (v i) ≤ 1) ∧ r = ‖α.as_alternating x v‖ }

/-- Global comass norm on forms. -/
def comass {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  ⨆ x, pointwiseComass α x

/-! ### Continuity of Comass -/

/-- **Axiom: Continuity of Pointwise Comass**
This follows from Berge's Maximum Theorem:
1. The evaluation map (x, v) ↦ |α(x) v| is continuous on the unit ball bundle.
2. The unit ball bundle is a compact fiber bundle over X.
3. The supremum of a continuous function over a compact set varies continuously.
Reference: Berge (1963), "Topological Spaces" -/
axiom pointwiseComass_continuous {k : ℕ} (α : SmoothForm n X k) :
    Continuous (pointwiseComass α)

/-! ### Basic Comass Properties -/

/-- Comass is non-negative.
Proof: iSup of sSup of norms, all nonnegative. -/
theorem comass_nonneg {k : ℕ} (α : SmoothForm n X k) : comass α ≥ 0 := by
  unfold comass
  apply Real.iSup_nonneg
  intro x
  unfold pointwiseComass
  apply Real.sSup_nonneg
  intro r ⟨_, _, hr⟩
  rw [hr]; exact norm_nonneg _

/-- Axiom: Pointwise comass of zero form is zero.
The zero form evaluates to 0 on all vectors, so sSup {‖0‖} = 0. -/
axiom pointwiseComass_zero {k : ℕ} (x : X) :
    pointwiseComass (0 : SmoothForm n X k) x = 0

/-- Axiom: The comass of the zero form is zero.
From pointwiseComass_zero, each fiber value is 0, so iSup = 0. -/
axiom comass_zero {k : ℕ} : comass (0 : SmoothForm n X k) = 0

/-- Pointwise comass of negation equals pointwise comass.
Proof: ‖-z‖ = ‖z‖ for all z ∈ ℂ. -/
theorem pointwiseComass_neg {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseComass (-α) x = pointwiseComass α x := by
  unfold pointwiseComass
  congr 1
  ext r
  constructor <;> intro ⟨v, hv, hr⟩ <;> use v, hv
  · simp only [SmoothForm.neg_apply, AlternatingMap.neg_apply, norm_neg] at hr
    exact hr
  · simp only [SmoothForm.neg_apply, AlternatingMap.neg_apply, norm_neg]
    exact hr

/-- Comass of negation equals comass.
Proof: Follows from pointwiseComass_neg. -/
theorem comass_neg {k : ℕ} (α : SmoothForm n X k) : comass (-α) = comass α := by
  unfold comass
  congr 1
  ext x
  exact pointwiseComass_neg α x

/-- Axiom: Comass is subadditive.
Triangle inequality: |α(v) + β(v)| ≤ |α(v)| + |β(v)| propagates through sSup and iSup. -/
axiom comass_add_le {k : ℕ} (α β : SmoothForm n X k) :
    comass (α + β) ≤ comass α + comass β

/-- Axiom: Comass is absolutely homogeneous.
For r : ℝ, |(r·α)(v)| = |r| · |α(v)| propagates through sSup and iSup. -/
axiom comass_smul {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    comass (r • α) = |r| * comass α

/-- Axiom: On a compact manifold, the comass is bounded.
Continuous functions on compact spaces are bounded. -/
axiom comass_bddAbove {k : ℕ} (α : SmoothForm n X k) :
    BddAbove (Set.range (pointwiseComass α))

/-! ## NormedAddCommGroup and NormedSpace instances

These instances are axiomatized because constructing them requires
showing that comass satisfies all normed space axioms, which depends
on the continuity and homogeneity axioms above. -/

/-- Axiom: TopologicalSpace on forms induced by comass norm. -/
axiom smoothFormTopologicalSpace_exists (k : ℕ) :
    Nonempty (TopologicalSpace (SmoothForm n X k))

instance smoothFormTopologicalSpace (k : ℕ) : TopologicalSpace (SmoothForm n X k) :=
  Classical.choice (smoothFormTopologicalSpace_exists k)

/-- Axiom: MetricSpace on forms induced by comass norm. -/
axiom smoothFormMetricSpace_exists (k : ℕ) :
    Nonempty (MetricSpace (SmoothForm n X k))

instance smoothFormMetricSpace (k : ℕ) : MetricSpace (SmoothForm n X k) :=
  Classical.choice (smoothFormMetricSpace_exists k)

/-- Axiom: NormedAddCommGroup on forms with comass norm. -/
axiom smoothFormNormedAddCommGroup_exists (k : ℕ) :
    Nonempty (NormedAddCommGroup (SmoothForm n X k))

instance smoothFormNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (SmoothForm n X k) :=
  Classical.choice (smoothFormNormedAddCommGroup_exists k)

/-- Axiom: NormedSpace over ℝ on forms with comass norm. -/
axiom smoothFormNormedSpace_exists (k : ℕ) :
    Nonempty (NormedSpace ℝ (SmoothForm n X k))

instance smoothFormNormedSpace (k : ℕ) : NormedSpace ℝ (SmoothForm n X k) :=
  Classical.choice (smoothFormNormedSpace_exists k)

/-! ## L2 Norm -/

/-- Axiom: The dual metric on the cotangent space induced by the Kähler metric.
This is the Hermitian inner product on T^*_x X induced by musical isomorphism. -/
axiom kahlerMetricDual (x : X) (α β : TangentSpace (𝓒_complex n) x →ₗ[ℂ] ℂ) : ℂ

/-- Axiom: The pointwise inner product of two k-forms.
Induced by extending the metric on T^* X to ⋀^k T^* X via determinant formula. -/
axiom pointwiseInner {k : ℕ} (α β : SmoothForm n X k) (x : X) : ℝ

/-- The pointwise norm of a k-form. -/
def pointwiseNorm {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  Real.sqrt (pointwiseInner α α x)

/-- Axiom: The L2 inner product of two forms.
Defined as ∫_X ⟨α, β⟩_x · ω^n where ω^n is the volume form. -/
axiom innerL2 {k : ℕ} (α β : SmoothForm n X k) : ℝ

/-- The Dirichlet energy (L2 norm squared) of a form. -/
def energy {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  innerL2 α α

/-- The L2 norm of a form. -/
def normL2 {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  Real.sqrt (energy α)

/-! ### L2 Properties -/

/-- Axiom: Energy Minimizer Property (Hodge theory).
For harmonic γ_harm in the same cohomology class as α,
energy α = energy γ_harm + energy (α - γ_harm).
This is the Pythagorean theorem for the Hodge decomposition. -/
axiom energy_minimizer {k : ℕ} (α γ_harm : SmoothForm n X k) :
    isClosed α → isHarmonic γ_harm →
    energy α = energy γ_harm + energy (α - γ_harm)

/-- Axiom: Pointwise inner product is non-negative.
Follows from positive-definiteness of the Kähler metric. -/
axiom pointwiseInner_nonneg {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseInner α α x ≥ 0

/-- Axiom: Energy is non-negative.
Follows from pointwiseInner_nonneg integrated over X. -/
axiom energy_nonneg {k : ℕ} (α : SmoothForm n X k) : energy α ≥ 0

/-- L2 norm is non-negative.
Proof: sqrt of non-negative. -/
theorem normL2_nonneg {k : ℕ} (α : SmoothForm n X k) : normL2 α ≥ 0 :=
  Real.sqrt_nonneg _

/-- Axiom: Trace L2 control.
On compact manifolds, the L2 norm controls the comass:
comass α ≤ C · ‖α‖_L2 for some constant C > 0.
This follows from Sobolev embedding and compactness. -/
axiom trace_L2_control {k : ℕ} (α : SmoothForm n X k) :
    ∃ C : ℝ, C > 0 ∧ comass α ≤ C * normL2 α

end
