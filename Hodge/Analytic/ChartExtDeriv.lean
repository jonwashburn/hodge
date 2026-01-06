import Hodge.Analytic.ContMDiffForms
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
Chart-level exterior derivative infrastructure (Stage 3 helper).

For a `ContMDiffForm n X k` and a basepoint `x₀ : X`, we define the coefficient function written
in the preferred chart at `x₀` and relate its model-space exterior derivative to our tangent-coordinate
expressions.

This file is **additive**: it does not modify the main `SmoothForm` layer.
-/

noncomputable section

open Classical Manifold
open scoped Manifold

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

namespace ContMDiffForm

variable {k : ℕ}

/-- A `ContMDiffForm` written in the preferred chart at a basepoint `x₀`.

This is the *model-space* coefficient map `E → FiberAlt n k` obtained by precomposing with
`(chartAt _ x₀).symm`. It is only intended to be used on `(chartAt _ x₀).target`. -/
noncomputable def omegaInChart (ω : ContMDiffForm n X k) (x₀ : X) :
    TangentModel n → FiberAlt n k :=
  fun u => ω.as_alternating ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u)

@[simp] lemma omegaInChart_apply (ω : ContMDiffForm n X k) (x₀ : X) (u : TangentModel n) :
    omegaInChart (n := n) (X := X) (k := k) ω x₀ u =
      ω.as_alternating ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u) := rfl

/-- Smoothness of the chart-coordinate coefficient map on the chart target. -/
theorem contDiffOn_omegaInChart (ω : ContMDiffForm n X k) (x₀ : X) :
    ContDiffOn ℂ ⊤ (omegaInChart (n := n) (X := X) (k := k) ω x₀)
      ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) := by
  -- `chartAt _ x₀`.symm is smooth on its target
  have hsymm :
      ContMDiffOn (𝓒_complex n) (𝓒_complex n) ⊤
        ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm)
        ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :=
    contMDiffOn_chart_symm (I := (𝓒_complex n)) (n := (⊤ : WithTop ℕ∞)) (x := x₀)

  -- ω is smooth on any set, in particular on `univ`
  have hω :
      ContMDiffOn (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤
        ω.as_alternating (Set.univ : Set X) := by
    simpa using (ω.smooth'.contMDiffOn (s := (Set.univ : Set X)))

  -- Compose: `ω ∘ chartAt.symm`
  have hcomp :
      ContMDiffOn (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤
        (fun u : TangentModel n =>
          ω.as_alternating ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u))
        ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :=
    (ContMDiffOn.comp (hg := hω) (hf := hsymm) (st := by simp))

  -- On the model space, `ContMDiffOn` is `ContDiffOn`.
  simpa [omegaInChart] using hcomp.contDiffOn

/-- The model-space exterior derivative of `ω` in the chart at `x₀`, using `extDerivWithin` on the
chart target. -/
noncomputable def extDerivInChartWithin (ω : ContMDiffForm n X k) (x₀ : X) :
    TangentModel n → FiberAlt n (k + 1) :=
  fun u =>
    _root_.extDerivWithin (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
      (omegaInChart (n := n) (X := X) (k := k) ω x₀)
      ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) u

/-- Smoothness of `extDerivInChartWithin` on the chart target. -/
theorem contDiffOn_extDerivInChartWithin (ω : ContMDiffForm n X k) (x₀ : X) :
    ContDiffOn ℂ ⊤ (extDerivInChartWithin (n := n) (X := X) (k := k) ω x₀)
      ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) := by
  -- `ω` in chart is `C^∞` on the chart target
  have hω : ContDiffOn ℂ ⊤ (omegaInChart (n := n) (X := X) (k := k) ω x₀)
      ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :=
    contDiffOn_omegaInChart (n := n) (X := X) (k := k) ω x₀
  -- Derivative is `C^∞` as well
  have hderiv :
      ContDiffOn ℂ ⊤
        (fderivWithin ℂ (omegaInChart (n := n) (X := X) (k := k) ω x₀)
          ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target))
        ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :=
    (hω.fderivWithin ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).open_target.uniqueDiffOn) (m := (⊤ : WithTop ℕ∞))
      (by simp))
  -- Compose with alternatization (a continuous linear map).
  let L :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (TangentModel n) ℂ (n := k)
  have hL : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun f => L f) :=
    ContinuousLinearMap.contDiff (𝕜 := ℂ)
      (E := (TangentModel n →L[ℂ] FiberAlt n k))
      (F := FiberAlt n (k + 1))
      (n := ⊤) L
  -- Now the claim is the chain rule.
  simpa [extDerivInChartWithin, _root_.extDerivWithin, L] using
    (hL.comp_contDiffOn hderiv)

/-- On the chart target (an open set), `extDerivWithin` agrees with `extDeriv`. -/
theorem extDerivInChartWithin_eq_extDeriv (ω : ContMDiffForm n X k) (x₀ : X)
    {u : TangentModel n} (hu : u ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :
    extDerivInChartWithin (n := n) (X := X) (k := k) ω x₀ u =
      _root_.extDeriv (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
        (omegaInChart (n := n) (X := X) (k := k) ω x₀) u := by
  -- Reduce to `fderivWithin_of_isOpen` on an open set.
  have hopen : IsOpen ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :=
    (chartAt (EuclideanSpace ℂ (Fin n)) x₀).open_target
  simp [extDerivInChartWithin, _root_.extDerivWithin, _root_.extDeriv,
    fderivWithin_of_isOpen hopen hu]

end ContMDiffForm
