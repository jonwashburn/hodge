import Hodge.Analytic.ContMDiffForms
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Basic

/-!
Chart-level exterior derivative infrastructure (Stage 3 helper).

For a `ContMDiffForm n X k` and a basepoint `x₀ : X`, we define the coefficient function written
in the preferred chart at `x₀` and relate its model-space exterior derivative to our tangent-coordinate
expressions.

This file is **additive**: it does not modify the main `SmoothForm` layer.
-/

noncomputable section

open Classical Manifold Filter
open scoped Manifold Topology

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
  have hsymm :
      ContMDiffOn (𝓒_complex n) (𝓒_complex n) ⊤
        ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm)
        ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :=
    contMDiffOn_chart_symm (I := (𝓒_complex n)) (n := (⊤ : WithTop ℕ∞)) (x := x₀)
  have hω :
      ContMDiffOn (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤
        ω.as_alternating (Set.univ : Set X) := by
    simpa using (ω.smooth'.contMDiffOn (s := (Set.univ : Set X)))
  have hcomp :
      ContMDiffOn (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤
        (fun u : TangentModel n =>
          ω.as_alternating ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u))
        ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :=
    (ContMDiffOn.comp (hg := hω) (hf := hsymm) (st := by simp))
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
  have hω : ContDiffOn ℂ ⊤ (omegaInChart (n := n) (X := X) (k := k) ω x₀)
      ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :=
    contDiffOn_omegaInChart (n := n) (X := X) (k := k) ω x₀
  have hderiv :
      ContDiffOn ℂ ⊤
        (fderivWithin ℂ (omegaInChart (n := n) (X := X) (k := k) ω x₀)
          ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target))
        ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :=
    (hω.fderivWithin ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).open_target.uniqueDiffOn) (m := (⊤ : WithTop ℕ∞))
      (by simp))
  let L :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (TangentModel n) ℂ (n := k)
  have hL : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun f => L f) :=
    ContinuousLinearMap.contDiff (𝕜 := ℂ)
      (E := (TangentModel n →L[ℂ] FiberAlt n k))
      (F := FiberAlt n (k + 1))
      (n := ⊤) L
  simpa [extDerivInChartWithin, _root_.extDerivWithin, L] using
    (hL.comp_contDiffOn hderiv)

/-- On the chart target (an open set), `extDerivWithin` agrees with `extDeriv`. -/
theorem extDerivInChartWithin_eq_extDeriv (ω : ContMDiffForm n X k) (x₀ : X)
    {u : TangentModel n} (hu : u ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :
    extDerivInChartWithin (n := n) (X := X) (k := k) ω x₀ u =
      _root_.extDeriv (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
        (omegaInChart (n := n) (X := X) (k := k) ω x₀) u := by
  have hopen : IsOpen ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).target) :=
    (chartAt (EuclideanSpace ℂ (Fin n)) x₀).open_target
  simp [extDerivInChartWithin, _root_.extDerivWithin, _root_.extDeriv,
    fderivWithin_of_isOpen hopen hu]

/-- On the diagonal (x = x₀), tangent coordinate change is identity.
    This is a special case that's easier to prove. -/
theorem mfderivInTangentCoordinates_eq_fderiv_diag (ω : ContMDiffForm n X k) (x₀ : X) :
    ω.mfderivInTangentCoordinates x₀ x₀ =
      fderiv ℂ (omegaInChart ω x₀) ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) x₀) := by
  -- On the diagonal, tangentCoordChange x₀ x₀ x₀ = id
  have hx₀_chart : x₀ ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := mem_chart_source _ x₀
  -- extChartAt source equals chartAt source for model-with-corners
  have hx₀ : x₀ ∈ (extChartAt (𝓒_complex n) x₀).source := by
    simp only [extChartAt_source]; exact hx₀_chart
  -- By mfderivInTangentCoordinates_eq, we have:
  -- mfderivInTangentCoordinates ω x₀ x₀ = mfderiv ω x₀ ∘L tangentCoordChange x₀ x₀ x₀
  have hmf := mfderivInTangentCoordinates_eq (n := n) (X := X) (k := k) ω x₀ x₀ hx₀_chart
  rw [hmf]
  -- tangentCoordChange x₀ x₀ x₀ = id on the diagonal
  have hdiag : tangentCoordChange (𝓒_complex n) x₀ x₀ x₀ = ContinuousLinearMap.id ℂ _ := by
    apply ContinuousLinearMap.ext
    intro v
    exact tangentCoordChange_self (I := 𝓒_complex n) (x := x₀) (z := x₀) (v := v) hx₀
  simp only [hdiag]
  -- Now we need: mfderiv (𝓒_complex n) 𝓘 ω.as_alternating x₀ = fderiv (omegaInChart ω x₀) (chartAt x₀ x₀)
  -- For model target 𝓘(ℂ, FiberAlt n k), mfderiv = fderiv in charts
  -- Since range (𝓒_complex n) = univ (boundaryless), mfderivWithin = mfderiv = fderivWithin univ = fderiv
  have hdiff : MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x₀ :=
    ω.smooth'.mdifferentiableAt (hn := by simp)
  -- mfderiv for model target equals fderiv of written form
  rw [hdiff.mfderiv]
  -- writtenInExtChartAt for trivial target model 𝓘 is just ω ∘ (extChartAt x₀).symm
  simp only [writtenInExtChartAt, Function.comp_def, ModelWithCorners.range_eq_univ,
    fderivWithin_univ]
  -- extChartAt for model-with-corners equals the underlying chartAt
  have hext : ∀ y, (extChartAt (𝓒_complex n) x₀) y = (chartAt (EuclideanSpace ℂ (Fin n)) x₀) y := by
    intro y; rfl
  have hext_symm : ∀ u, (extChartAt (𝓒_complex n) x₀).symm u = (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u := by
    intro u; rfl
  -- The target chart is trivial (identity)
  have htarget : ∀ v, (extChartAt 𝓘(ℂ, FiberAlt n k) (ω.as_alternating x₀)) v = v := by
    intro v; rfl
  simp only [htarget, hext, hext_symm]
  -- Now we have: fderiv (ω.as_alternating ∘ (chartAt x₀).symm) (chartAt x₀ x₀)
  -- which equals fderiv (omegaInChart ω x₀) (chartAt x₀ x₀) by definition
  rfl

/-- The manifold derivative in tangent coordinates matches the fderiv of the chart representation.

    **Proof sketch**:
    1. `mfderivInTangentCoordinates ω x₀ x = mfderiv ω x ∘L tangentCoordChange x₀ x` (by `mfderivInTangentCoordinates_eq`)
    2. For the target space `𝓘(ℂ, FiberAlt n k)`, `mfderiv` reduces to `fderiv` in charts (by `mfderivWithin_eq_fderivWithin`).
    3. The composition `ω.as_alternating ∘ (chartAt x₀).symm` equals `omegaInChart ω x₀` by definition.
    4. By the chain rule for `fderiv`, we get the result.

    **Technical requirement**: Relating `tangentCoordChange x₀ x` to chart transition maps. -/
theorem mfderivInTangentCoordinates_eq_fderiv (ω : ContMDiffForm n X k) (x₀ x : X)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source) :
    ω.mfderivInTangentCoordinates x₀ x =
      fderiv ℂ (omegaInChart ω x₀) ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) x) := by
  -- 1. Apply `mfderivInTangentCoordinates_eq`
  rw [mfderivInTangentCoordinates_eq (n := n) (X := X) (k := k) ω x₀ x hx]
  
  -- 2. Expand `mfderiv` in charts using `writtenInExtChartAt`
  have hdiff : MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x :=
    ω.smooth'.mdifferentiableAt (hn := by simp)
  rw [hdiff.mfderiv]
  
  -- 3. Simplify chart representations
  simp only [writtenInExtChartAt, Function.comp_def, ModelWithCorners.range_eq_univ,
    fderivWithin_univ]
  have hext : ∀ y, (extChartAt (𝓒_complex n) x) y = (chartAt (EuclideanSpace ℂ (Fin n)) x) y := by
    intro y; rfl
  have hext_symm : ∀ u, (extChartAt (𝓒_complex n) x).symm u = (chartAt (EuclideanSpace ℂ (Fin n)) x).symm u := by
    intro u; rfl
  have htarget : ∀ v, (extChartAt 𝓘(ℂ, FiberAlt n k) (ω.as_alternating x)) v = v := by
    intro v; rfl
  simp only [htarget, hext, hext_symm]

  -- 4. Identify `tangentCoordChange` with `fderiv` of transition map
  let ψ := (chartAt (EuclideanSpace ℂ (Fin n)) x) ∘ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm
  let u₀ := (chartAt (EuclideanSpace ℂ (Fin n)) x₀) x
  
  have h_trans : tangentCoordChange (𝓒_complex n) x₀ x x = fderiv ℂ ψ u₀ := by
    rw [tangentCoordChange_def]
    rw [ModelWithCorners.range_eq_univ, fderivWithin_univ]
    congr 1
    ext z
    dsimp [ψ]
    simp only [Function.comp_apply]
    rw [hext_symm, hext]

  rw [h_trans]

  -- 5. Define functions for Chain Rule
  let g := ω.as_alternating ∘ (chartAt (EuclideanSpace ℂ (Fin n)) x).symm
  let f := ψ
  
  -- Verify `f u₀ = (chartAt x) x`
  have h_comp_pt : f u₀ = (chartAt (EuclideanSpace ℂ (Fin n)) x) x := by
    dsimp [f, ψ, u₀]
    simp only [Function.comp_apply]
    -- (chartAt x) ( (chartAt x₀).symm (chartAt x₀ x) ) = (chartAt x) x
    rw [(chartAt (EuclideanSpace ℂ (Fin n)) x₀).left_inv hx]

  -- 6. Apply Chain Rule
  
  -- Differentiability assumptions
  have hf_diff : DifferentiableAt ℂ f u₀ := by
    -- The transition map is smooth
    sorry

  have hg_diff : DifferentiableAt ℂ g (f u₀) := by
    rw [h_comp_pt]
    have h_written := hdiff.differentiableWithinAt_writtenInExtChartAt
    rw [ModelWithCorners.range_eq_univ] at h_written
    exact h_written.differentiableAt Filter.univ_mem

  -- Apply fderiv_comp
  -- The current goal has `(fderiv g (chartAt x x)) ∘ (fderiv f u₀)`
  -- We substitute `chartAt x x` with `f u₀`
  rw [← h_comp_pt]
  -- Match the goal to use f instead of ψ
  change (fderiv ℂ g (f u₀)).comp (fderiv ℂ f u₀) = _
  
  -- Apply chain rule
  -- fderiv_comp : fderiv (g ∘ f) x = fderiv g (f x) ∘ fderiv f x
  -- We want to replace RHS with LHS
  rw [← fderiv_comp (x := u₀) hg_diff hf_diff]
  
  -- 7. Show composition is omegaInChart
  -- We need to show fderiv (g ∘ f) = fderiv (omegaInChart ...)
  -- They are equal if the functions agree on a neighborhood
  apply Filter.EventuallyEq.fderiv_eq
  -- The neighborhood is the chart target intersected with the preimage of the other chart source
  let U := (chartAt (EuclideanSpace ℂ (Fin n)) x₀).target ∩ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm ⁻¹' (chartAt (EuclideanSpace ℂ (Fin n)) x).source
  apply Filter.eventually_of_mem (s := U)
  · show U ∈ 𝓝 u₀
    apply IsOpen.mem_nhds
    · apply IsOpen.inter
      · exact (chartAt (EuclideanSpace ℂ (Fin n)) x₀).open_target
      · apply IsOpen.preimage
        · exact (chartAt (EuclideanSpace ℂ (Fin n)) x₀).continuousOn_symm.continuousAt (mem_chart_target _ _).1
        · exact (chartAt (EuclideanSpace ℂ (Fin n)) x).open_source
    · simp only [u₀, mem_inter_iff, mem_chart_target]
      constructor
      · exact (mem_chart_target _ _).2
      · simp only [mem_preimage, LocalEquiv.symm_apply_apply]
        exact mem_chart_source _ x
  · intro z hz
    simp only [U, mem_inter_iff, mem_preimage] at hz
    simp only [g, f, ψ, Function.comp_apply, omegaInChart_apply]
    rw [LocalEquiv.left_inv]
    exact hz.2

/-- The manifold-level pointwise exterior derivative `extDerivAt` matches the model-space
    `extDeriv` of the chart representation, transported back to basepoint coordinates.

    **Proof sketch**:
    1. Apply `mfderivInTangentCoordinates_eq_fderiv` to express `mfderiv` in chart coordinates.
    2. Use the definition of `extDeriv` as `alternatizeUncurryFin ∘ fderiv`.
    3. The transport via `tangentCoordChange` relates the two coordinate systems. -/
theorem extDerivAt_eq_extDeriv (ω : ContMDiffForm n X k) (x₀ x : X)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source) :
    ω.extDerivAt x =
      ((_root_.extDeriv (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
          (omegaInChart ω x₀) ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) x)).compContinuousLinearMap
        (tangentCoordChange (𝓒_complex n) x x₀ x)) := by
  -- Follows from mfderivInTangentCoordinates_eq_fderiv and alternatization properties.
  sorry

end ContMDiffForm
