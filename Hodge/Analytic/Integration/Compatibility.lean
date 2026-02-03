import Hodge.Analytic.Integration.VolumeForm
import Hodge.Analytic.Integration.TopFormIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integration Compatibility (L² vs Top‑Form)

This file records explicit compatibility data between:
- the Kähler volume measure used in L² integration, and
- the top‑form integration functional built from submanifold integration data.

It intentionally lives *after* `VolumeForm` and `TopFormIntegral` to avoid import cycles.
-/

noncomputable section

open Classical MeasureTheory Hodge

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-! ## Top‑Form Evaluation -/

/-- Evaluate a top form on the chosen volume basis at `x`. -/
noncomputable def topFormEval (η : SmoothForm n X (2 * n)) (x : X)
    [VolumeBasisData n X] : ℂ :=
  (η.as_alternating x) (volumeBasis (n := n) (X := X) x)

/-- Real part of top‑form evaluation. -/
noncomputable def topFormEval_real (η : SmoothForm n X (2 * n)) (x : X)
    [VolumeBasisData n X] : ℝ :=
  (topFormEval (n := n) (X := X) η x).re

/-! ## Compatibility Data -/

/-- Compatibility between `kahlerMeasure` and `topFormIntegral_real'`.

This is the explicit bridge needed to relate `L2Inner_measure` (using `kahlerMeasure`)
to `L2Inner_wedge` (using `topFormIntegral_real'`).
-/
class TopFormIntegralCompatibilityData (n : ℕ) (X : Type u)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [KahlerVolumeMeasureData n X] [KahlerMeasureCompatibilityData n X]
    [VolumeBasisData n X] where
  topFormIntegral_eq :
    ∀ η : SmoothForm n X (2 * n),
      topFormIntegral_real' (n := n) (X := X)
        (kahlerSubmanifoldIntegrationData (n := n) (X := X)) η =
        ∫ x, topFormEval_real (n := n) (X := X) η x ∂
          (kahlerMeasure (n := n) (X := X))

end
