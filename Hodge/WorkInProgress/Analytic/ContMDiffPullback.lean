import Hodge.Analytic.Advanced.ContMDiffForms
import Hodge.WorkInProgress.Analytic.Pullback
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

noncomputable section

open Classical Manifold
open scoped Manifold

namespace ContMDiffForm

set_option autoImplicit false

universe u

variable {n : ℕ} {k : ℕ}
variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
variable {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) Y] [IsManifold (𝓒_complex n) ⊤ Y]

/-- Chart-level representation of a map `f` in coordinates at `x₀`. -/
noncomputable def fChart (f : X → Y) (x₀ : X) : TangentModel n → TangentModel n :=
  fun u =>
    (chartAt (EuclideanSpace ℂ (Fin n)) (f x₀))
      (f ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u))

lemma mfderiv_eq_fderiv_fChart (f : X → Y) (x₀ y : X)
    [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n Y]
    (hx : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy : f y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (f x₀)).source)
    (hf : MDifferentiableAt (𝓒_complex n) (𝓒_complex n) f y) :
    mfderiv (𝓒_complex n) (𝓒_complex n) f y =
      fderiv ℝ (fChart (n := n) f x₀)
        ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) y) := by
  classical
  -- Charts are locally constant on chart sources.
  have hchart :
      chartAt (EuclideanSpace ℂ (Fin n)) y =
        chartAt (EuclideanSpace ℂ (Fin n)) x₀ :=
    (HasLocallyConstantCharts.hCharts (n := n) (X := X) (x := x₀) (y := y) hx)
  have hchart_f :
      chartAt (EuclideanSpace ℂ (Fin n)) (f y) =
        chartAt (EuclideanSpace ℂ (Fin n)) (f x₀) :=
    (HasLocallyConstantCharts.hCharts (n := n) (X := Y) (x := f x₀) (y := f y) hy)
  -- Simplify the written-in-chart expression to `fChart`.
  have h_written :
      writtenInExtChartAt (𝓒_complex n) (𝓒_complex n) y f =
        fChart (n := n) f x₀ := by
    funext u
    simp [writtenInExtChartAt, fChart, extChartAt_coe, extChartAt_coe_symm,
      𝓒_complex, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      hchart, hchart_f]
  -- Range of the model with corners is all of `TangentModel n`.
  have h_range : Set.range (𝓒_complex n) = (Set.univ : Set (TangentModel n)) := by
    simp [𝓒_complex, modelWithCornersSelf_coe, Set.range_id]
  -- Now unfold `mfderiv` and rewrite.
  simp [mfderiv, hf, h_range, fderivWithin_univ, h_written,
    extChartAt_coe, 𝓒_complex, modelWithCornersSelf_coe, hchart]

/-- Pullback of a `ContMDiffForm` (WIP). -/
noncomputable def pullbackFun (f : X → Y) (ω : ContMDiffForm n Y k) : X → FiberAlt n k :=
  fun x =>
    fiberPullback (n := n)
      (mfderiv (𝓒_complex n) (𝓒_complex n) f x) (ω.as_alternating (f x))

/-- Pullback of a `ContMDiffForm` along a smooth map (WIP). -/
noncomputable def pullback (f : X → Y) (ω : ContMDiffForm n Y k) :
    ContMDiffForm n X k :=
  { as_alternating := pullbackFun (n := n) (f := f) ω
    smooth' := by
      -- TODO: show smoothness using `ContMDiff` of `f` and `ω`.
      sorry }

@[simp] lemma pullback_as_alternating (f : X → Y) (ω : ContMDiffForm n Y k) (x : X) :
    (pullback (n := n) (f := f) ω).as_alternating x =
      fiberPullback (n := n)
        (mfderiv (𝓒_complex n) (𝓒_complex n) f x) (ω.as_alternating (f x)) := rfl

/-- Pullback commutes with `extDerivForm` (WIP). -/
theorem extDerivForm_pullback {k : ℕ} (f : X → Y) (ω : ContMDiffForm n Y k)
    [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n Y] :
    extDerivForm (pullback (n := n) (f := f) ω) HasLocallyConstantCharts.hCharts =
      pullback (n := n) (f := f) (extDerivForm ω HasLocallyConstantCharts.hCharts) := by
  -- Reduce to a pointwise statement on `extDerivAt`.
  ext x
  -- Unfold `extDerivForm` to `extDerivAt`.
  simp [extDerivForm_as_alternating, extDeriv_as_alternating, pullback_as_alternating,
    pullbackFun]
  -- Work in the preferred chart at `x`.
  -- This is a chart-level pullback identity; see `extDeriv_pullback` in Mathlib.
  set x₀ : X := x
  set y₀ : Y := f x₀
  set u₀ : TangentModel n := (chartAt (EuclideanSpace ℂ (Fin n)) x₀) x₀
  -- Chart-level representation of `f` at `x₀`.
  let f_chart : TangentModel n → TangentModel n :=
    fun u =>
      (chartAt (EuclideanSpace ℂ (Fin n)) y₀) (f ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u))
  -- Use the chart-level exterior derivative at `u₀`.
  have h_ext_pullback :
      _root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k)
        (fun u =>
          (omegaInChart ω y₀ (f_chart u)).compContinuousLinearMap
            (fderiv ℝ f_chart u)) u₀ =
        ( _root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k) (omegaInChart ω y₀)
            (f_chart u₀)).compContinuousLinearMap (fderiv ℝ f_chart u₀) := by
    -- Apply the Euclidean pullback lemma.
    -- `omegaInChart ω y₀` is smooth, and `f_chart` is smooth in charts.
    -- TODO: supply the `ContDiffAt` and `DifferentiableAt` hypotheses for `extDeriv_pullback`.
    sorry
  -- Compare the manifold `extDerivAt` to chart-level `extDeriv`.
  have h_chart_pull :
      extDerivAt (pullback (n := n) (f := f) ω) x₀ =
        _root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k)
          (omegaInChart (pullback (n := n) (f := f) ω) x₀) u₀ := by
    simpa [x₀, u₀] using (extDerivAt_eq_chart_extDeriv (ω := pullback (n := n) (f := f) ω) x₀)
  have h_chart_ω :
      extDerivAt ω y₀ =
        _root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k)
          (omegaInChart ω y₀) (f_chart u₀) := by
    -- `f_chart u₀ = (chartAt y₀) y₀`
    have : f_chart u₀ = (chartAt (EuclideanSpace ℂ (Fin n)) y₀) y₀ := by
      simp [f_chart, u₀, y₀]
    simpa [this, y₀] using (extDerivAt_eq_chart_extDeriv (ω := ω) y₀)
  -- TODO: show the chart-level pullback coincides with `omegaInChart (pullback f ω) x₀` near `u₀`.
  -- Then the chart-level lemma `h_ext_pullback` implies the desired identity.
  -- This requires identifying `mfderiv f` with the chart derivative of `f_chart`.
  sorry

@[simp] lemma pullback_toSmoothForm (f : X → Y) (ω : ContMDiffForm n Y k) :
    (pullback (n := n) (f := f) ω).toSmoothForm =
      smoothFormPullback (n := n) (f := f) ω.toSmoothForm := rfl

end ContMDiffForm
