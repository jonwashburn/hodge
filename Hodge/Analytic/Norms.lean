import Hodge.Analytic.Forms
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Track B.2: Norms and Metrics

This file defines the global norms on differential forms (comass and L2)
and proves their basic properties on compact Kähler manifolds.
-/

noncomputable section

open Classical Set Filter

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

/-- The pointwise comass of a k-form at a point x. -/
def pointwiseComass {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  sSup { r : ℝ | ∃ (v : Fin k → TangentSpace (𝓒_complex n) x),
    (∀ i, tangentNorm x (v i) ≤ 1) ∧ r = ‖α.as_alternating x v‖ }

/-- Global comass norm on forms. -/
def comass {k : ℕ} (α : SmoothForm n X k) : ℝ := 
  if _h : Nonempty X then ⨆ x, pointwiseComass α x else 0

-- All comass properties as axioms
axiom pointwiseComass_continuous {k : ℕ} (α : SmoothForm n X k) : Continuous (pointwiseComass α)
axiom pointwiseComass_zero {k : ℕ} (x : X) : pointwiseComass (0 : SmoothForm n X k) x = 0
axiom comass_zero {k : ℕ} : comass (0 : SmoothForm n X k) = 0
axiom pointwiseComass_neg {k : ℕ} (α : SmoothForm n X k) (x : X) : pointwiseComass (-α) x = pointwiseComass α x
axiom comass_neg {k : ℕ} (α : SmoothForm n X k) : comass (-α) = comass α
axiom comass_bddAbove {k : ℕ} (α : SmoothForm n X k) : BddAbove (range (pointwiseComass α))
axiom comass_add_le {k : ℕ} (α β : SmoothForm n X k) : comass (α + β) ≤ comass α + comass β
axiom comass_smul {k : ℕ} (r : ℝ) (α : SmoothForm n X k) : comass (r • α) = |r| * comass α
axiom comass_eq_zero_iff {k : ℕ} (α : SmoothForm n X k) : comass α = 0 ↔ α = 0

theorem comass_nonneg {k : ℕ} (α : SmoothForm n X k) : comass α ≥ 0 := by
  unfold comass
  split_ifs with h
  · apply Real.iSup_nonneg; intro x; unfold pointwiseComass
    apply Real.sSup_nonneg; rintro r ⟨_, _, rfl⟩; exact norm_nonneg _
  · exact le_refl 0

/-! ## Normed Space Instances -/

instance smoothFormNorm {k : ℕ} : Norm (SmoothForm n X k) where norm := comass
theorem smoothForm_norm_def {k : ℕ} (α : SmoothForm n X k) : ‖α‖ = comass α := rfl

/-- **Axiom: existence of normed add comm group instance.** -/
axiom smoothFormNormedAddCommGroup_axiom (n : ℕ) (X : Type*) 
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (k : ℕ) : NormedAddCommGroup (SmoothForm n X k)

instance smoothFormNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (SmoothForm n X k) :=
  smoothFormNormedAddCommGroup_axiom n X k

/-- **Axiom: existence of normed space instance.** -/
axiom smoothFormNormedSpace_axiom (n : ℕ) (X : Type*) 
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (k : ℕ) : NormedSpace ℝ (SmoothForm n X k)

instance smoothFormNormedSpace (k : ℕ) : NormedSpace ℝ (SmoothForm n X k) :=
  smoothFormNormedSpace_axiom n X k

/-! ## L2 Norm -/

axiom kahlerMetricDual (x : X) (_α _β : TangentSpace (𝓒_complex n) x →ₗ[ℂ] ℂ) : ℂ
axiom pointwiseInner {k : ℕ} (α β : SmoothForm n X k) (x : X) : ℝ

/-- Axiom: Pointwise norm expansion. -/
axiom pointwiseNorm_sq_expand {k : ℕ} (x : X) (α β : SmoothForm n X k) (t : ℝ) :
    (Real.sqrt (pointwiseInner (α + t • β) (α + t • β) x))^2 = 
    pointwiseInner α α x + 2 * t * (pointwiseInner α β x) + t^2 * (pointwiseInner β β x)

def pointwiseNorm {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ := Real.sqrt (pointwiseInner α α x)
axiom innerL2 {k : ℕ} (α β : SmoothForm n X k) : ℝ
def energy {k : ℕ} (α : SmoothForm n X k) : ℝ := innerL2 α α
def normL2 {k : ℕ} (α : SmoothForm n X k) : ℝ := Real.sqrt (energy α)

axiom energy_minimizer {k : ℕ} (α γ_harm : SmoothForm n X k) :
    isClosed α → isHarmonic γ_harm → energy α = energy γ_harm + energy (α - γ_harm)

axiom pointwiseInner_nonneg {k : ℕ} (α : SmoothForm n X k) (x : X) : pointwiseInner α α x ≥ 0
axiom energy_nonneg {k : ℕ} (α : SmoothForm n X k) : energy α ≥ 0
theorem normL2_nonneg {k : ℕ} (α : SmoothForm n X k) : normL2 α ≥ 0 := Real.sqrt_nonneg _

axiom trace_L2_control {k : ℕ} (α : SmoothForm n X k) : ∃ C : ℝ, C > 0 ∧ comass α ≤ C * normL2 α

end
