import Hodge.Analytic.Forms
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
Stage 2 groundwork: a manifold-aware (chart-based) smoothness layer for forms.

The main development currently uses `SmoothForm n X k`, whose coefficients are only assumed
`Continuous`. This is sufficient for the “closed proof skeleton”, but blocks a real exterior
derivative `d`.

This file introduces an *opt-in* `C^∞` variant, where the coefficient map
`X → FiberAlt n k` is `ContMDiff`. For such forms we can at least define the **pointwise**
exterior derivative using Mathlib’s manifold derivative `mfderiv` and alternatization.

We intentionally do **not** replace `Hodge.Analytic.Forms.extDerivLinearMap` yet:
upgrading the global `SmoothForm`-based cohomology layer requires a larger migration (Stage 2/3),
and would destabilize the current end-to-end proof.
-/

noncomputable section

open Classical Manifold

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-- A `C^∞` `k`-form in the *current* (fiberwise) representation: a smooth map
`X → FiberAlt n k`. -/
structure ContMDiffForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  as_alternating : X → FiberAlt n k
  smooth' : ContMDiff (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤ as_alternating

namespace ContMDiffForm

instance (k : ℕ) : CoeFun (ContMDiffForm n X k) (fun _ => X → FiberAlt n k) where
  coe ω := ω.as_alternating

/-- Forgetful map to the existing `SmoothForm` (which only remembers continuity). -/
def toSmoothForm {k : ℕ} (ω : ContMDiffForm n X k) : SmoothForm n X k :=
  ⟨ω.as_alternating, by
    -- `C^∞` implies continuous.
    simpa [IsSmoothAlternating] using (ω.smooth'.continuous)⟩

@[simp] lemma toSmoothForm_as_alternating {k : ℕ} (ω : ContMDiffForm n X k) :
    ω.toSmoothForm.as_alternating = ω.as_alternating := rfl

/-!
### Pointwise exterior derivative

For `ω : X → FiberAlt n k`, the manifold derivative `mfderiv` is defined everywhere (as `0`
when not differentiable). For `C^∞` forms it agrees with the intended derivative in charts.

We define the **pointwise** exterior derivative by alternatizing `mfderiv`.
Making this into a globally `ContMDiff` (or even `Continuous`) section is the key remaining
technical step for Stage 2.
-/

/-- The pointwise exterior derivative of a `C^∞` form, as a fiber element. -/
noncomputable def extDerivAt {k : ℕ} (ω : ContMDiffForm n X k) (x : X) : FiberAlt n (k + 1) :=
  -- `mfderiv` lands in `TangentSpace (𝓒_complex n) x →L[ℂ] FiberAlt n k`,
  -- and in this complex-manifold model that domain is definitionaly `TangentModel n`.
  ContinuousAlternatingMap.alternatizeUncurryFin
    (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
    (by
      -- coerce `mfderiv` into the fixed model-space type
      simpa using
        (mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x))

@[simp] lemma extDerivAt_def {k : ℕ} (ω : ContMDiffForm n X k) (x : X) :
    ω.extDerivAt x =
      ContinuousAlternatingMap.alternatizeUncurryFin
        (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
        (by
          simpa using
            (mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x)) := rfl

/-!
### Differentiability facts

These lemmas are useful when upgrading `extDerivAt` from a pointwise definition to a genuine
`SmoothForm` (i.e. when proving continuity/smoothness of `x ↦ extDerivAt ω x`).
-/

theorem mdifferentiableAt {k : ℕ} (ω : ContMDiffForm n X k) (x : X) :
    MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x :=
  (ω.smooth'.contMDiffAt.mdifferentiableAt (by simp))

/-!
### Smoothness of `mfderiv` in tangent coordinates (local statement)

Mathlib’s lemma `ContMDiffAt.mfderiv` gives smoothness of the derivative map after expressing it in
bundle trivializations (`inTangentCoordinates`).  This is the right “chart-level” statement for
Stage 2.

In our development, `SmoothForm` uses a *fixed* model-space fiber representation, so the remaining
technical step is to relate this `inTangentCoordinates` statement to the desired global smoothness
of the coefficient map `x ↦ mfderiv … ω.as_alternating x` (and hence `x ↦ extDerivAt ω x`).
-/

/-- The derivative `mfderiv` packaged as a map into a fixed model-space of linear maps,
expressed in the standard bundle trivializations at a basepoint `x₀`. -/
noncomputable def mfderivInTangentCoordinates {k : ℕ} (ω : ContMDiffForm n X k) (x₀ : X) :
    X → (TangentModel n →L[ℂ] FiberAlt n k) :=
  inTangentCoordinates (𝓒_complex n) 𝓘(ℂ, FiberAlt n k)
    (fun x : X => x)
    (fun x : X => ω.as_alternating x)
    (fun x : X => mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x)
    x₀

theorem contMDiffAt_mfderivInTangentCoordinates {k : ℕ} (ω : ContMDiffForm n X k) (x₀ : X) :
    ContMDiffAt (𝓒_complex n) 𝓘(ℂ, TangentModel n →L[ℂ] FiberAlt n k) ⊤
      (mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀) x₀ := by
  -- Use Mathlib’s specialized lemma `ContMDiffAt.mfderiv_const` (`g = id`, no parameters).
  have hf : ContMDiffAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤ ω.as_alternating x₀ :=
    ω.smooth'.contMDiffAt
  have hmn : (⊤ : WithTop ℕ∞) + 1 ≤ (⊤ : WithTop ℕ∞) := by simp
  simpa [mfderivInTangentCoordinates] using
    (ContMDiffAt.mfderiv_const
      (𝕜 := ℂ)
      (I := (𝓒_complex n))
      (I' := 𝓘(ℂ, FiberAlt n k))
      (f := ω.as_alternating)
      (x₀ := x₀)
      (m := (⊤ : WithTop ℕ∞))
      (n := (⊤ : WithTop ℕ∞))
      hf hmn)

/-- The pointwise exterior derivative built from `mfderivInTangentCoordinates`.

This is the natural “coordinate-level” upgrade of `extDerivAt`: we first express the manifold
derivative in tangent-bundle coordinates (relative to a basepoint `x₀`), then alternatize. -/
noncomputable def extDerivInTangentCoordinates {k : ℕ} (ω : ContMDiffForm n X k) (x₀ : X) :
    X → FiberAlt n (k + 1) :=
  fun x =>
    ContinuousAlternatingMap.alternatizeUncurryFin
      (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
      (mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀ x)

theorem contMDiffAt_extDerivInTangentCoordinates {k : ℕ} (ω : ContMDiffForm n X k) (x₀ : X) :
    ContMDiffAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n (k + 1)) ⊤
      (extDerivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀) x₀ := by
  -- Compose the `ContMDiffAt` derivative-in-coordinates map with the (smooth) alternatization CLM.
  let L :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (TangentModel n) ℂ (n := k)
  have hL : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun a : (TangentModel n →L[ℂ] FiberAlt n k) => L a) := by
    -- `L` is a continuous linear map, hence `C^∞`.
    simpa using
      (ContinuousLinearMap.contDiff
        (𝕜 := ℂ)
        (E := (TangentModel n →L[ℂ] FiberAlt n k))
        (F := FiberAlt n (k + 1))
        (n := (⊤ : WithTop ℕ∞))
        L)
  have hm :
      ContMDiffAt (𝓒_complex n) 𝓘(ℂ, TangentModel n →L[ℂ] FiberAlt n k) ⊤
        (mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀) x₀ :=
    contMDiffAt_mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀
  -- Use the general `ContDiff.comp_contMDiffAt`.
  have := ContDiff.comp_contMDiffAt (I := (𝓒_complex n)) (g := fun a => L a) (f := mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀)
    (x := x₀) hL hm
  simpa [extDerivInTangentCoordinates, L] using this

end ContMDiffForm
