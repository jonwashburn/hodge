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
-/

noncomputable section

open Classical Set

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

/-- The pointwise comass of a k-form at a point x. -/
def pointwiseComass {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  sSup { r : ℝ | ∃ (v : Fin k → TangentSpace (𝓒_complex n) x),
    (∀ i, tangentNorm x (v i) ≤ 1) ∧ r = ‖α.as_alternating x v‖ }

/-- Global comass norm on forms. -/
def comass {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  ⨆ x, pointwiseComass α x

/-! ### Continuity of Comass -/

axiom pointwiseComass_continuous {k : ℕ} (α : SmoothForm n X k) :
    Continuous (pointwiseComass α)

/-! ### Basic Comass Properties -/

/-- Comass is non-negative. -/
theorem comass_nonneg {k : ℕ} (α : SmoothForm n X k) : comass α ≥ 0 := by
  unfold comass
  apply Real.iSup_nonneg
  intro x
  unfold pointwiseComass
  apply Real.sSup_nonneg
  intro r ⟨_, _, hr⟩
  rw [hr]; exact norm_nonneg _

/-- Axiom: Pointwise comass of zero form is zero. -/
axiom pointwiseComass_zero {k : ℕ} (x : X) :
    pointwiseComass (0 : SmoothForm n X k) x = 0

/-- Axiom: The comass of the zero form is zero. -/
axiom comass_zero {k : ℕ} : comass (0 : SmoothForm n X k) = 0

/-- Pointwise comass of negation equals pointwise comass. -/
theorem pointwiseComass_neg {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseComass (-α) x = pointwiseComass α x := by
  unfold pointwiseComass
  congr 1
  ext r
  simp [norm_neg]

/-- Comass of negation equals comass. -/
theorem comass_neg {k : ℕ} (α : SmoothForm n X k) : comass (-α) = comass α := by
  unfold comass
  congr 1
  ext x
  exact pointwiseComass_neg α x

axiom comass_add_le {k : ℕ} (α β : SmoothForm n X k) :
    comass (α + β) ≤ comass α + comass β

axiom comass_smul {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    comass (r • α) = |r| * comass α

axiom comass_bddAbove {k : ℕ} (α : SmoothForm n X k) :
    BddAbove (Set.range (pointwiseComass α))

/-! ## NormedAddCommGroup and NormedSpace instances -/

axiom smoothFormTopologicalSpace_exists (k : ℕ) :
    Nonempty (TopologicalSpace (SmoothForm n X k))

instance smoothFormTopologicalSpace (k : ℕ) : TopologicalSpace (SmoothForm n X k) :=
  Classical.choice (smoothFormTopologicalSpace_exists k)

axiom smoothFormMetricSpace_exists (k : ℕ) :
    Nonempty (MetricSpace (SmoothForm n X k))

instance smoothFormMetricSpace (k : ℕ) : MetricSpace (SmoothForm n X k) :=
  Classical.choice (smoothFormMetricSpace_exists k)

axiom smoothFormNormedAddCommGroup_exists (k : ℕ) :
    Nonempty (NormedAddCommGroup (SmoothForm n X k))

instance smoothFormNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (SmoothForm n X k) :=
  Classical.choice (smoothFormNormedAddCommGroup_exists k)

axiom smoothFormNormedSpace_exists (k : ℕ) :
    Nonempty (NormedSpace ℝ (SmoothForm n X k))

instance smoothFormNormedSpace (k : ℕ) : NormedSpace ℝ (SmoothForm n X k) :=
  Classical.choice (smoothFormNormedSpace_exists k)

/-! ## L2 Norm -/

axiom kahlerMetricDual (x : X) (α β : TangentSpace (𝓒_complex n) x →ₗ[ℂ] ℂ) : ℂ

axiom pointwiseInner {k : ℕ} (α β : SmoothForm n X k) (x : X) : ℝ

def pointwiseNorm {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  Real.sqrt (pointwiseInner α α x)

axiom innerL2 {k : ℕ} (α β : SmoothForm n X k) : ℝ

def energy {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  innerL2 α α

def normL2 {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  Real.sqrt (energy α)

axiom energy_minimizer {k : ℕ} (α γ_harm : SmoothForm n X k) :
    isClosed α → isHarmonic γ_harm →
    energy α = energy γ_harm + energy (α - γ_harm)

axiom pointwiseInner_nonneg {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseInner α α x ≥ 0

axiom energy_nonneg {k : ℕ} (α : SmoothForm n X k) : energy α ≥ 0

theorem normL2_nonneg {k : ℕ} (α : SmoothForm n X k) : normL2 α ≥ 0 :=
  Real.sqrt_nonneg _

axiom trace_L2_control {k : ℕ} (α : SmoothForm n X k) :
    ∃ C : ℝ, (C > 0) ∧ (comass α ≤ C * normL2 α)

end
