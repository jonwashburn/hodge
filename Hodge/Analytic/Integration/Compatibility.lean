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

@[simp] lemma topFormEval_real_add (η₁ η₂ : SmoothForm n X (2 * n)) (x : X)
    [VolumeBasisData n X] :
    topFormEval_real (n := n) (X := X) (η₁ + η₂) x =
      topFormEval_real (n := n) (X := X) η₁ x +
        topFormEval_real (n := n) (X := X) η₂ x := by
  simp [topFormEval_real, topFormEval, SmoothForm.add_apply, Complex.add_re]

@[simp] lemma topFormEval_real_smul (r : ℝ) (η : SmoothForm n X (2 * n)) (x : X)
    [VolumeBasisData n X] :
    topFormEval_real (n := n) (X := X) (r • η) x =
      r * topFormEval_real (n := n) (X := X) η x := by
  simp [topFormEval_real, topFormEval, SmoothForm.smul_real_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.zero_mul]

/-! ## Top-degree integration data -/

/-- Data for integrating top forms against a fixed measure using `topFormEval_real`. -/
class TopDegreeIntegrationData (n : ℕ) (X : Type u)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [VolumeBasisData n X] where
  measure : Measure X
  finite : measure Set.univ < ∞
  integrable_topFormEval :
    ∀ η : SmoothForm n X (2 * n),
      Integrable (fun x => topFormEval_real (n := n) (X := X) η x) measure

/-- Top-form integral defined directly by measure integration of `topFormEval_real`. -/
noncomputable def topFormIntegral_real_measure (data : TopDegreeIntegrationData n X)
    (η : SmoothForm n X (2 * n)) : ℝ :=
  ∫ x, topFormEval_real (n := n) (X := X) η x ∂data.measure

theorem topFormIntegral_real_measure_add (data : TopDegreeIntegrationData n X)
    (η₁ η₂ : SmoothForm n X (2 * n)) :
    topFormIntegral_real_measure (n := n) (X := X) data (η₁ + η₂) =
      topFormIntegral_real_measure (n := n) (X := X) data η₁ +
        topFormIntegral_real_measure (n := n) (X := X) data η₂ := by
  have h1 := data.integrable_topFormEval η₁
  have h2 := data.integrable_topFormEval η₂
  simp [topFormIntegral_real_measure, topFormEval_real_add,
    MeasureTheory.integral_add h1 h2]

theorem topFormIntegral_real_measure_smul (data : TopDegreeIntegrationData n X)
    (r : ℝ) (η : SmoothForm n X (2 * n)) :
    topFormIntegral_real_measure (n := n) (X := X) data (r • η) =
      r * topFormIntegral_real_measure (n := n) (X := X) data η := by
  have hη := data.integrable_topFormEval η
  simp [topFormIntegral_real_measure, topFormEval_real_smul,
    MeasureTheory.integral_const_mul, hη]

/-- Build top-degree integration data from explicit submanifold integration data,
given integrability of the top-form evaluation. -/
noncomputable def topDegreeIntegrationData_ofSubmanifold
    (data : SubmanifoldIntegrationData n X)
    [VolumeBasisData n X]
    (h_integrable :
      ∀ η : SmoothForm n X (2 * n),
        Integrable (fun x => topFormEval_real (n := n) (X := X) η x)
          (data.measure2p n)) :
    TopDegreeIntegrationData n X :=
  { measure := data.measure2p n
    finite := data.measure2p_finite n
    integrable_topFormEval := h_integrable }

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

/-! ### Concrete constructor -/

/-- Build `TopFormIntegralCompatibilityData` from explicit submanifold integration data,
provided a matching top-form evaluation lemma. -/
noncomputable def topFormIntegralCompatibilityData_ofSubmanifold
    (data : SubmanifoldIntegrationData n X)
    [VolumeBasisData n X]
    (h_top :
      ∀ η : SmoothForm n X (2 * n),
        topFormIntegral_real' (n := n) (X := X) data η =
          ∫ x, topFormEval_real (n := n) (X := X) η x ∂
            (data.measure2p n)) :
    TopFormIntegralCompatibilityData n X := by
  -- Provide the canonical Kähler measure and compatibility from the given data.
  letI : KahlerVolumeMeasureData n X :=
    kahlerVolumeMeasureData_ofSubmanifold (n := n) (X := X) data
  letI : KahlerMeasureCompatibilityData n X :=
    kahlerMeasureCompatibilityData_ofSubmanifold (n := n) (X := X) data
  refine { topFormIntegral_eq := ?_ }
  intro η
  -- Reduce to the supplied top-form lemma; the Kähler measure is definitional here.
  simpa using (h_top η)

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

/-- Express `L2Inner` in terms of `L2Inner_measure` for the Kähler volume measure. -/
theorem L2Inner_eq_L2Inner_measure_kahler
    [KahlerVolumeMeasureData n X] [CompactSpace X]
    {k : ℕ} (α β : SmoothForm n X k) :
    _root_.L2Inner (n := n) (X := X) (k := k) α β =
      Hodge.Analytic.L2.L2Inner_measure (n := n) (X := X) (k := k)
        (μ := kahlerMeasure (n := n) (X := X)) α β := by
  classical
  -- Use the canonical `VolumeIntegrationData` built from the Kähler measure.
  letI : VolumeIntegrationData n X :=
    volumeIntegrationData_kahlerMeasure (n := n) (X := X)
  simpa using
    (Hodge.Analytic.L2.L2Inner_eq_L2Inner_measure_ofMeasure (n := n) (X := X) (k := k)
      (μ := kahlerMeasure (n := n) (X := X)) α β)

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

/-- Bridge `L2Inner` to `L2Inner_wedge` using explicit compatibility data. -/
theorem L2Inner_wedge_eq_L2Inner
    [KahlerVolumeMeasureData n X] [KahlerMeasureCompatibilityData n X]
    [VolumeBasisData n X] [TopFormIntegralCompatibilityData n X]
    [L2InnerWedgeCompatibilityData n X] [CompactSpace X]
    {k : ℕ} (hk : k ≤ 2 * n) (α β : SmoothForm n X k) :
    L2Inner_wedge (n := n) (X := X) (k := k) hk
        (kahlerSubmanifoldIntegrationData (n := n) (X := X)) α β =
      _root_.L2Inner (n := n) (X := X) (k := k) α β := by
  -- First, relate the wedge pairing to the measure-based L² pairing.
  have hwedge :=
    L2Inner_wedge_eq_L2Inner_measure (n := n) (X := X) (k := k) hk α β
  -- Then identify `L2Inner` with `L2Inner_measure` for the Kähler measure.
  have hL2 :=
    (L2Inner_eq_L2Inner_measure_kahler (n := n) (X := X) (k := k) α β).symm
  exact hwedge.trans hL2

end
