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

/-! ## Wedge‑Star Evaluation -/

/-- Evaluate `α ∧ ⋆β` against the volume basis (real part), with an explicit degree cast. -/
noncomputable def topFormEval_real_wedge {k : ℕ} (hk : k ≤ 2 * n)
    (α β : SmoothForm n X k) (x : X) [VolumeBasisData n X] : ℝ :=
  topFormEval_real (n := n) (X := X)
    (castForm (by exact Nat.add_sub_of_le hk) (α ⋏ ⋆β)) x

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

/-- Compatibility between `pointwiseInner` and `α ∧ ⋆β` evaluation. -/
class L2InnerWedgeCompatibilityData (n : ℕ) (X : Type u)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [VolumeBasisData n X] where
  pointwiseInner_eq_topFormEval_wedge :
    ∀ {k : ℕ} (hk : k ≤ 2 * n) (α β : SmoothForm n X k) (x : X),
      pointwiseInner (n := n) (X := X) (k := k) α β x =
        topFormEval_real_wedge (n := n) (X := X) hk α β x

/-! ## L² vs Wedge Compatibility -/

/-- Bridge `L2Inner_measure` (Kähler measure) to `L2Inner_wedge` (top‑form integration). -/
theorem L2Inner_wedge_eq_L2Inner_measure
    [KahlerVolumeMeasureData n X] [KahlerMeasureCompatibilityData n X]
    [VolumeBasisData n X] [TopFormIntegralCompatibilityData n X]
    [L2InnerWedgeCompatibilityData n X]
    {k : ℕ} (hk : k ≤ 2 * n) (α β : SmoothForm n X k) :
    L2Inner_wedge (n := n) (X := X) (k := k) hk
        (kahlerSubmanifoldIntegrationData (n := n) (X := X)) α β =
      Hodge.Analytic.L2.L2Inner_measure (n := n) (X := X) (k := k)
        (μ := kahlerMeasure (n := n) (X := X)) α β := by
  classical
  -- Unfold the wedge-based definition and use the explicit top-form compatibility.
  unfold L2Inner_wedge
  have hdeg : k + (2 * n - k) = 2 * n := by
    exact Nat.add_sub_of_le hk
  -- Convert the top-form integral to a measure integral of top-form evaluation.
  have htop :
      topFormIntegral_real' (n := n) (X := X)
          (kahlerSubmanifoldIntegrationData (n := n) (X := X))
          (castForm hdeg (α ⋏ ⋆β)) =
        ∫ x, topFormEval_real (n := n) (X := X)
            (castForm hdeg (α ⋏ ⋆β)) x ∂
          (kahlerMeasure (n := n) (X := X)) := by
    simpa using (TopFormIntegralCompatibilityData.topFormIntegral_eq (n := n) (X := X)
      (η := castForm hdeg (α ⋏ ⋆β)))
  -- Rewrite the integrand using the pointwise compatibility.
  have hpoint :
      (fun x =>
          topFormEval_real (n := n) (X := X) (castForm hdeg (α ⋏ ⋆β)) x) =
        fun x => pointwiseInner (n := n) (X := X) (k := k) α β x := by
    funext x
    have h :=
      L2InnerWedgeCompatibilityData.pointwiseInner_eq_topFormEval_wedge
        (n := n) (X := X) (k := k) hk α β x
    -- `topFormEval_real_wedge` is definitional, so we can unfold it.
    simpa [topFormEval_real_wedge] using h.symm
  -- Combine everything.
  simpa [Hodge.Analytic.L2.L2Inner_measure, hpoint] using htop

end
