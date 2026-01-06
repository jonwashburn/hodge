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

variable {k : ℕ}

/-- The pointwise exterior derivative of a `C^∞` form, as a fiber element. -/
noncomputable def extDerivAt (ω : ContMDiffForm n X k) (x : X) : FiberAlt n (k + 1) :=
  ContinuousAlternatingMap.alternatizeUncurryFin
    (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
    (mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x)

@[simp] lemma extDerivAt_def (ω : ContMDiffForm n X k) (x : X) :
    ω.extDerivAt x =
      ContinuousAlternatingMap.alternatizeUncurryFin
        (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
        (mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x) := rfl

/-!
### Differentiability facts

These lemmas are useful when upgrading `extDerivAt` from a pointwise definition to a genuine
`SmoothForm` (i.e. when proving continuity/smoothness of `x ↦ extDerivAt ω x`).
-/

/-- Helper: `mfderiv` expressed in tangent coordinates relative to a basepoint `x₀`. -/
noncomputable def mfderivInTangentCoordinates (ω : ContMDiffForm n X k) (x₀ x : X) :
    TangentModel n →L[ℂ] FiberAlt n k :=
  inTangentCoordinates (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) (fun y => y) (fun y => ω.as_alternating y)
    (fun y => mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating y) x₀ x

/-- Smoothness of the tangent-coordinate expression of the derivative.
    This follows from `ContMDiffAt.mfderiv_const` (since the fiber bundle for values is trivial). -/
theorem contMDiffAt_mfderivInTangentCoordinates (ω : ContMDiffForm n X k) (x₀ : X) :
    ContMDiffAt (𝓒_complex n) 𝓘(ℂ, TangentModel n →L[ℂ] FiberAlt n k) ⊤
      (mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀) x₀ := by
  -- ω.as_alternating is smooth
  have hf : ContMDiffAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤ ω.as_alternating x₀ :=
    ω.smooth' x₀
  -- Use Mathlib's `ContMDiffAt.mfderiv_const`.
  simpa [mfderivInTangentCoordinates] using
    ContMDiffAt.mfderiv_const (I := 𝓒_complex n) (I' := 𝓘(ℂ, FiberAlt n k))
      (f := ω.as_alternating) (x₀ := x₀) hf (by simp)

/-- The pointwise exterior derivative built from `mfderivInTangentCoordinates`.

This is the natural “coordinate-level” upgrade of `extDerivAt`: we first express the manifold
derivative in tangent-bundle coordinates (relative to a basepoint `x₀`), then alternatize. -/
noncomputable def extDerivInTangentCoordinates (ω : ContMDiffForm n X k) (x₀ : X) :
    X → FiberAlt n (k + 1) :=
  fun x =>
    ContinuousAlternatingMap.alternatizeUncurryFin
      (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
      (mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀ x)

theorem contMDiffAt_extDerivInTangentCoordinates (ω : ContMDiffForm n X k) (x₀ : X) :
    ContMDiffAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n (k + 1)) ⊤
      (extDerivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀) x₀ := by
  -- Compose the `ContMDiffAt` derivative-in-coordinates map with the (smooth) alternatization CLM.
  let L :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (TangentModel n) ℂ (n := k)
  have hL : ContDiff ℂ (⊤ : WithTop ℕ∞) ⇑L :=
    ContinuousLinearMap.contDiff (𝕜 := ℂ)
      (E := (TangentModel n) →L[ℂ] FiberAlt n k)
      (F := FiberAlt n (k + 1))
      (n := ⊤)
      L
  have hm :
      ContMDiffAt (𝓒_complex n) 𝓘(ℂ, TangentModel n →L[ℂ] FiberAlt n k) ⊤
        (mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀) x₀ :=
    contMDiffAt_mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀
  -- Use the general `ContDiff.comp_contMDiffAt`.
  have := ContDiff.comp_contMDiffAt (I := (𝓒_complex n)) (g := ⇑L) (f := mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀)
    (x := x₀) hL hm
  simpa [extDerivInTangentCoordinates, L] using this

/-- The global exterior derivative operator for `ContMDiffForm`.
    It maps a smooth form to a smooth form. The smoothness proof is currently admitted
    (`sorry`) to unblock integration; it relies on the fact that `extDerivAt` corresponds
    to the diagonal of the smooth coordinate expression `extDerivInTangentCoordinates`. -/
noncomputable def extDeriv (ω : ContMDiffForm n X k) : ContMDiffForm n X (k + 1) where
  as_alternating := extDerivAt ω
  smooth' := by
    -- TODO: Formalize the diagonal smoothness argument.
    -- We know `extDerivInTangentCoordinates ω x₀ x` is smooth in `x` (for fixed `x₀`)
    -- and intuitively smooth in `x₀` (dependence on chart). The diagonal map
    -- `x ↦ extDerivInTangentCoordinates ω x x` coincides with `x ↦ extDerivAt ω x`
    -- because `inTangentCoordinates` is identity on the diagonal.
    sorry

end ContMDiffForm
