import Hodge.Analytic.Norms
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# L² inner product via measure integration (infrastructure)

This file provides a **genuine** (Bochner) integral-based `L2Inner` for the existing
`pointwiseInner` defined in `Hodge/Analytic/Norms.lean`.

Important:
- The main proof track for `hodge_conjecture'` does **not** use this file.
- We keep this measure-theoretic development in `Hodge/Analytic/Integration/*` to avoid
  pulling MeasureTheory into core norm/comass infrastructure on the main track.

Mathematically, on a compact Kähler manifold \(X\), one wants:
\[
  \langle \alpha, \beta \rangle_{L^2} := \int_X \langle \alpha, \beta \rangle_x \, dV
\]
where \(dV\) is the Riemannian volume measure.

In this repo, we parameterize by an arbitrary finite measure `μ : Measure X`; choosing the
“right” `μ` (Kähler volume) is handled elsewhere.
-/

noncomputable section

open Classical
open scoped BigOperators

namespace Hodge
namespace Analytic
namespace L2

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

section Measure

open MeasureTheory

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-!
## Integrability of `pointwiseInner`

On a compact space, a continuous real-valued function is bounded. Together with
`[IsFiniteMeasure μ]`, this implies integrability.
-/

private theorem pointwiseInner_integrable {k : ℕ} (μ : Measure X) [IsFiniteMeasure μ]
    (α β : SmoothForm n X k) :
    Integrable (fun x => pointwiseInner (n := n) (X := X) (k := k) α β x) μ := by
  classical
  -- 1) `pointwiseInner α β` is continuous.
  have hcont :
      Continuous (fun x => pointwiseInner (n := n) (X := X) (k := k) α β x) :=
    (KahlerMetricData.fromFrame n X k).inner_continuous α β
  -- 2) Hence it is a.e.-measurable, hence a.e.-strongly measurable.
  have hAEMeas :
      AEMeasurable (fun x => pointwiseInner (n := n) (X := X) (k := k) α β x) μ :=
    (Continuous.aemeasurable hcont)
  have hAES :
      AEStronglyMeasurable (fun x => pointwiseInner (n := n) (X := X) (k := k) α β x) μ :=
    hAEMeas.aestronglyMeasurable
  -- 3) Boundedness (via compactness of the range of the norm).
  let g : X → ℝ := fun x =>
    ‖pointwiseInner (n := n) (X := X) (k := k) α β x‖
  have hcont_g : Continuous g := continuous_norm.comp hcont
  have hbdd : BddAbove (Set.range g) := by
    apply IsCompact.bddAbove
    apply isCompact_range
    exact hcont_g
  rcases hbdd with ⟨C, hC⟩
  have hbound : ∀ x, ‖pointwiseInner (n := n) (X := X) (k := k) α β x‖ ≤ C := by
    intro x
    -- `g x ∈ range g`
    have hx : g x ∈ Set.range g := ⟨x, rfl⟩
    exact hC hx
  have hbound_ae :
      ∀ᵐ x ∂μ, ‖pointwiseInner (n := n) (X := X) (k := k) α β x‖ ≤ C :=
    Filter.Eventually.of_forall hbound
  -- 4) Conclude integrability from boundedness on a finite measure space.
  exact Integrable.of_bound hAES C hbound_ae

/-!
## The L² inner product (measure version)
-/

/-- Measure-based global \(L^2\) inner product:

`⟪α,β⟫_μ := ∫ x, pointwiseInner α β x ∂μ`.

This is the intended “volume integration” definition; to recover the classical `L²` pairing,
instantiate `μ` with the Kähler/Riemannian volume measure. -/
noncomputable def L2Inner_measure {k : ℕ} (μ : Measure X)
    (α β : SmoothForm n X k) : ℝ :=
  ∫ x, pointwiseInner (n := n) (X := X) (k := k) α β x ∂μ

theorem L2Inner_measure_add_left {k : ℕ} (μ : Measure X) [IsFiniteMeasure μ]
    (α₁ α₂ β : SmoothForm n X k) :
    L2Inner_measure (n := n) (X := X) (k := k) μ (α₁ + α₂) β =
      L2Inner_measure (n := n) (X := X) (k := k) μ α₁ β +
        L2Inner_measure (n := n) (X := X) (k := k) μ α₂ β := by
  -- Rewrite the integrand using pointwise linearity, then use `integral_add`.
  have h_point :
      (fun x => pointwiseInner (n := n) (X := X) (k := k) (α₁ + α₂) β x) =
        (fun x => pointwiseInner (n := n) (X := X) (k := k) α₁ β x +
          pointwiseInner (n := n) (X := X) (k := k) α₂ β x) := by
    funext x
    -- `pointwiseInner` is `K.inner` where `K := KahlerMetricData.fromFrame`.
    simpa [pointwiseInner] using
      (KahlerMetricData.fromFrame n X k).inner_add_left α₁ α₂ β x
  have h1 : Integrable (fun x => pointwiseInner (n := n) (X := X) (k := k) α₁ β x) μ :=
    pointwiseInner_integrable (n := n) (X := X) (k := k) μ α₁ β
  have h2 : Integrable (fun x => pointwiseInner (n := n) (X := X) (k := k) α₂ β x) μ :=
    pointwiseInner_integrable (n := n) (X := X) (k := k) μ α₂ β
  -- Now compute.
  simp [L2Inner_measure, h_point, MeasureTheory.integral_add h1 h2]

theorem L2Inner_measure_smul_left {k : ℕ} (μ : Measure X) [IsFiniteMeasure μ]
    (r : ℝ) (α β : SmoothForm n X k) :
    L2Inner_measure (n := n) (X := X) (k := k) μ (r • α) β =
      r * L2Inner_measure (n := n) (X := X) (k := k) μ α β := by
  have h_point :
      (fun x => pointwiseInner (n := n) (X := X) (k := k) (r • α) β x) =
        fun x => r * pointwiseInner (n := n) (X := X) (k := k) α β x := by
    funext x
    simpa [pointwiseInner] using
      (KahlerMetricData.fromFrame n X k).inner_smul_left r α β x
  simp [L2Inner_measure, h_point, MeasureTheory.integral_const_mul]

theorem L2Inner_measure_comm {k : ℕ} (μ : Measure X) (α β : SmoothForm n X k) :
    L2Inner_measure (n := n) (X := X) (k := k) μ α β =
      L2Inner_measure (n := n) (X := X) (k := k) μ β α := by
  -- Follows from symmetry of `pointwiseInner`.
  have h_point :
      (fun x => pointwiseInner (n := n) (X := X) (k := k) α β x) =
        fun x => pointwiseInner (n := n) (X := X) (k := k) β α x := by
    funext x
    simpa using pointwiseInner_comm (n := n) (X := X) (k := k) α β x
  simp [L2Inner_measure, h_point]

theorem L2Inner_measure_self_nonneg {k : ℕ} (μ : Measure X) (α : SmoothForm n X k) :
    0 ≤ L2Inner_measure (n := n) (X := X) (k := k) μ α α := by
  -- `integral_nonneg` works with pointwise nonnegativity.
  have h_point : (0 : X → ℝ) ≤ fun x => pointwiseInner (n := n) (X := X) (k := k) α α x := by
    intro x
    exact pointwiseInner_self_nonneg (n := n) (X := X) (k := k) α x
  simpa [L2Inner_measure] using (MeasureTheory.integral_nonneg h_point)

end Measure

/-!
## Convenience: use the ambient `volume` measure

This avoids threading an explicit `μ : Measure X` when a `MeasureSpace X` instance is already
available and intended to represent the Kähler/Riemannian volume measure.
-/

section Volume

open MeasureTheory

variable [MeasureSpace X] [OpensMeasurableSpace X] [IsFiniteMeasure (volume : Measure X)]

/-- The \(L^2\) inner product integrated against the ambient `volume` measure. -/
noncomputable abbrev L2Inner_volume {k : ℕ} (α β : SmoothForm n X k) : ℝ :=
  L2Inner_measure (n := n) (X := X) (k := k) (μ := (volume : Measure X)) α β

end Volume

end L2
end Analytic
end Hodge
