import Hodge.Analytic.FormType
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
open scoped Manifold

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

/-!
### Convenience: `Boundaryless` instance for the complex model

Mathlib provides `Boundaryless` for the trivial model `𝓘(ℂ, TangentModel n)`. The model
`𝓒_complex n` is definitional equal to this, but typeclass search does not always unfold it.
We register the instance explicitly so lemmas that require `[I.Boundaryless]` can be used
without manual `change` steps.
-/

instance instBoundaryless_Ccomplex : (𝓒_complex n).Boundaryless := by
  -- `𝓒_complex n` is defeq to `𝓘(ℂ, TangentModel n)`
  change (𝓘(ℂ, TangentModel n)).Boundaryless
  infer_instance

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

/-- When `x` lies in the source of the preferred chart at `x₀`, `mfderivInTangentCoordinates`
is explicitly `mfderiv` precomposed with the tangent coordinate change from `x₀` to `x`.

This is the concrete form of `inTangentCoordinates_eq` specialized to our trivial target model. -/
theorem mfderivInTangentCoordinates_eq (ω : ContMDiffForm n X k) (x₀ x : X)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source) :
    mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀ x =
      (mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x : TangentModel n →L[ℂ] FiberAlt n k)
        ∘L (tangentCoordChange (𝓒_complex n) x₀ x x) := by
  classical
  have hy : ω.as_alternating x ∈ (chartAt (FiberAlt n k) (ω.as_alternating x₀)).source := by
    simpa using (mem_chart_source (FiberAlt n k) (ω.as_alternating x₀))
  have h :=
    (inTangentCoordinates_eq (I := (𝓒_complex n)) (I' := 𝓘(ℂ, FiberAlt n k))
        (f := fun y : X => y) (g := fun y : X => ω.as_alternating y)
        (ϕ := fun y : X =>
          (mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating y : TangentModel n →L[ℂ] FiberAlt n k))
        (x₀ := x₀) (x := x) hx hy)
  -- The target is a model space, so the target coordinate change collapses; the source is `tangentCoordChange`.
  simpa [mfderivInTangentCoordinates, inTangentCoordinates, tangentCoordChange] using h

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

/-!
### Transport of alternating maps along tangent coordinate changes (Stage 3 helper)

To relate “transported” `(k+1)`-forms to the raw `mfderiv` output, we need a compatibility lemma
between alternatization and pullback along a linear map.

Concretely, if `A : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F`, then pulling back `alternatizeUncurryFin A` along
`L : E →L[𝕜] E` corresponds to alternatizing the conjugated linear map
`compContinuousLinearMapCLM L ∘L A ∘L L`.
-/

section TransportAlternating

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- `Fin.removeNth` commutes with postcomposition by a linear map. -/
private lemma fin_removeNth_comp' {n : ℕ} (L : E →L[𝕜] E) (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    i.removeNth (⇑L ∘ v) = (⇑L ∘ i.removeNth v) := by
  funext j
  simp [Fin.removeNth]

/-- Pullback of `alternatizeUncurryFin` along a linear map can be pushed inside alternatization. -/
theorem alternatizeUncurryFin_compContinuousLinearMap {n : ℕ}
    (A : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) (L : E →L[𝕜] E) :
    (ContinuousAlternatingMap.alternatizeUncurryFin A).compContinuousLinearMap L =
      ContinuousAlternatingMap.alternatizeUncurryFin
        (ContinuousAlternatingMap.compContinuousLinearMapCLM L ∘L A ∘L L) := by
  ext v
  simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, fin_removeNth_comp']

end TransportAlternating

/-!
### Invertibility of `tangentCoordChange` on overlaps

On the overlap of the domains of two extended charts, the tangent coordinate change maps
`(tangentCoordChange I x y z)` and `(tangentCoordChange I y x z)` are inverses (as continuous linear maps).

We record this explicitly, as it is frequently used when transporting forms between coordinate systems.
-/

section TangentCoordChangeInv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem tangentCoordChange_comp_eq_id {x y z : M}
    (hz : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source) :
    (tangentCoordChange I x y z).comp (tangentCoordChange I y x z) = (1 : E →L[𝕜] E) := by
  ext v
  have h3 :
      z ∈ (extChartAt I y).source ∩ (extChartAt I x).source ∩ (extChartAt I y).source := by
    refine ⟨⟨hz.2, hz.1⟩, hz.2⟩
  have hcomp := (tangentCoordChange_comp (w := y) (x := x) (y := y) (z := z) (v := v) (I := I) h3)
  -- `tangentCoordChange I x y z (tangentCoordChange I y x z v) = tangentCoordChange I y y z v`
  simpa [ContinuousLinearMap.comp_apply] using
    (by simpa using (hcomp.trans (tangentCoordChange_self (I := I) (x := y) (z := z) (v := v) hz.2)))

theorem tangentCoordChange_comp_eq_id' {x y z : M}
    (hz : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source) :
    (tangentCoordChange I y x z).comp (tangentCoordChange I x y z) = (1 : E →L[𝕜] E) := by
  -- symmetric statement
  simpa [and_left_comm, and_assoc, and_comm] using
    (tangentCoordChange_comp_eq_id (I := I) (x := y) (y := x) (z := z) ⟨hz.2, hz.1⟩)

end TangentCoordChangeInv

/-!
### Correct transported coordinate representation of `extDerivAt` (Stage 3 milestone)

The object `extDerivInTangentCoordinates ω x₀` records the derivative in tangent coordinates as a
map `E →L (E [⋀^Fin k]→L F)` and then alternatizes. If we *transport* the resulting `(k+1)`-form value
at `x` back to basepoint coordinates at `x₀` (pullback along the tangent coordinate change), we must
also transport the intermediate `k`-forms appearing in the derivative. Concretely, the transport
adds a factor `compContinuousLinearMapCLM` on the `k`-form output.

The definition below packages this corrected transported expression and proves that it matches the
transport of `extDerivAt` on the chart neighborhood of `x₀`.
-/

/-- The **transported** coordinate expression for `dω` relative to a basepoint `x₀`.

This is designed so that for `x` in the chart domain of `x₀`, it agrees with transporting the
pointwise exterior derivative `ω.extDerivAt x` back to basepoint coordinates at `x₀`. -/
noncomputable def extDerivInTangentCoordinatesTransported (ω : ContMDiffForm n X k) (x₀ : X) :
    X → FiberAlt n (k + 1) :=
  fun x =>
    ContinuousAlternatingMap.alternatizeUncurryFin
      (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (tangentCoordChange (𝓒_complex n) x₀ x x) ∘L
        mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀ x)

/-- On the chart neighborhood of `x₀`, the transported coordinate expression agrees with
transporting the pointwise exterior derivative. -/
theorem extDerivInTangentCoordinatesTransported_eq (ω : ContMDiffForm n X k) (x₀ x : X)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source) :
    extDerivInTangentCoordinatesTransported (n := n) (X := X) (k := k) ω x₀ x =
      (extDerivAt (n := n) (X := X) (k := k) ω x).compContinuousLinearMap
        (tangentCoordChange (𝓒_complex n) x₀ x x) := by
  -- Use the explicit formula for `mfderivInTangentCoordinates` then apply the transport lemma for alternatization.
  have hmf :
      mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀ x =
        (mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x : TangentModel n →L[ℂ] FiberAlt n k) ∘L
          (tangentCoordChange (𝓒_complex n) x₀ x x) :=
    mfderivInTangentCoordinates_eq (n := n) (X := X) (k := k) ω x₀ x hx
  simp [extDerivInTangentCoordinatesTransported, extDerivAt, hmf,
    alternatizeUncurryFin_compContinuousLinearMap]

/-!
### A (currently unbundled) exterior derivative operator

At this stage we only define the *pointwise* exterior derivative `extDerivAt`.
Proving that `x ↦ extDerivAt ω x` is `ContMDiff` (hence can be bundled back into a
`ContMDiffForm`) requires a chart-gluing argument and is deferred.
-/

/-- The exterior derivative as an unbundled map on coefficient functions. -/
noncomputable def extDeriv (ω : ContMDiffForm n X k) : X → FiberAlt n (k + 1) :=
  extDerivAt ω

/-!
### Algebraic structure

We now define the basic algebraic operations on `ContMDiffForm` (zero, add, neg, smul)
so that the type forms a module over ℂ.
-/

/-- The zero `k`-form. -/
noncomputable def zero : ContMDiffForm n X k where
  as_alternating := fun _ => 0
  smooth' := contMDiff_const

instance : Zero (ContMDiffForm n X k) := ⟨zero⟩

@[simp] lemma zero_as_alternating (x : X) : (0 : ContMDiffForm n X k).as_alternating x = 0 := rfl

/-- Addition of `ContMDiffForm`s is pointwise. -/
noncomputable def add (ω η : ContMDiffForm n X k) : ContMDiffForm n X k where
  as_alternating := fun x => ω.as_alternating x + η.as_alternating x
  smooth' := by
    let addCLM : (FiberAlt n k × FiberAlt n k) →L[ℂ] FiberAlt n k :=
      ContinuousLinearMap.fst ℂ (FiberAlt n k) (FiberAlt n k) +
      ContinuousLinearMap.snd ℂ (FiberAlt n k) (FiberAlt n k)
    exact addCLM.contMDiff.comp (ContMDiff.prodMk_space ω.smooth' η.smooth')

instance : Add (ContMDiffForm n X k) := ⟨add⟩

@[simp] lemma add_as_alternating (ω η : ContMDiffForm n X k) (x : X) :
    (ω + η).as_alternating x = ω.as_alternating x + η.as_alternating x := rfl

/-- Negation of a `ContMDiffForm` is pointwise. -/
noncomputable def neg (ω : ContMDiffForm n X k) : ContMDiffForm n X k where
  as_alternating := fun x => -ω.as_alternating x
  smooth' := by
    let negCLM : FiberAlt n k →L[ℂ] FiberAlt n k := -ContinuousLinearMap.id ℂ (FiberAlt n k)
    exact negCLM.contMDiff.comp ω.smooth'

instance : Neg (ContMDiffForm n X k) := ⟨neg⟩

@[simp] lemma neg_as_alternating (ω : ContMDiffForm n X k) (x : X) :
    (-ω).as_alternating x = -ω.as_alternating x := rfl

/-- Scalar multiplication of a `ContMDiffForm` is pointwise. -/
noncomputable def smul (c : ℂ) (ω : ContMDiffForm n X k) : ContMDiffForm n X k where
  as_alternating := fun x => c • ω.as_alternating x
  smooth' := by
    let smulCLM : FiberAlt n k →L[ℂ] FiberAlt n k := c • ContinuousLinearMap.id ℂ (FiberAlt n k)
    exact smulCLM.contMDiff.comp ω.smooth'

instance : SMul ℂ (ContMDiffForm n X k) := ⟨smul⟩

@[simp] lemma smul_as_alternating (c : ℂ) (ω : ContMDiffForm n X k) (x : X) :
    (c • ω).as_alternating x = c • ω.as_alternating x := rfl

/-!
### Extensionality

-/

@[ext]
theorem ext (ω η : ContMDiffForm n X k) (h : ∀ x, ω.as_alternating x = η.as_alternating x) :
    ω = η := by
  cases ω; cases η; congr; funext x; exact h x

/-!
### Linearity of the exterior derivative

The exterior derivative is a linear map: `d(ω + η) = dω + dη` and `d(c • ω) = c • dω`.
-/

/-- The exterior derivative is additive: `d(ω + η) = dω + dη`.

    **Mathematical Justification**:
    1. `mfderiv (f + g) = mfderiv f + mfderiv g` (from Mathlib's `mfderiv_add`)
    2. `alternatizeUncurryFin` is linear (it's a continuous linear map)
    3. Therefore, `d(ω + η) = alternatize(mfderiv(ω + η)) = alternatize(mfderiv ω + mfderiv η)
                          = alternatize(mfderiv ω) + alternatize(mfderiv η) = dω + dη`

    **Type-theoretic note**: The proof requires careful handling because `mfderiv` returns
    a map between `TangentSpace` types that vary with the point. For complex manifolds
    modeled on `EuclideanSpace ℂ (Fin n)`, these are all definitionally equal to the model
    space, but Lean's type class resolution doesn't always unify them automatically.

    **Implementation note**: We use Mathlib's `mfderiv_add` together with the lemma
    `ContinuousAlternatingMap.alternatizeUncurryFin_add`. -/
theorem extDerivAt_add (ω η : ContMDiffForm n X k) (x : X) :
    extDerivAt (ω + η) x = extDerivAt ω x + extDerivAt η x := by
  simp only [extDerivAt_def]
  have h_add : (ω + η).as_alternating = ω.as_alternating + η.as_alternating := rfl
  rw [h_add]
  have hω : MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x :=
    ω.smooth'.mdifferentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
  have hη : MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) η.as_alternating x :=
    η.smooth'.mdifferentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
  have hmf :=
    mfderiv_add (I := (𝓒_complex n)) (E' := FiberAlt n k)
      (f := ω.as_alternating) (g := η.as_alternating) (z := x) hω hη
  rw [hmf]
  simp

/-- The exterior derivative commutes with scalars: `d(c • ω) = c • dω`.

    **Mathematical Justification**:
    1. `mfderiv (c • f) = c • mfderiv f` (from Mathlib's `const_smul_mfderiv`)
    2. `alternatizeUncurryFin` commutes with scalars (it's a linear map)
    3. Therefore, `d(c • ω) = alternatize(mfderiv(c • ω)) = alternatize(c • mfderiv ω)
                           = c • alternatize(mfderiv ω) = c • dω`

    **Implementation note**: We use Mathlib's `const_smul_mfderiv` together with the lemma
    `ContinuousAlternatingMap.alternatizeUncurryFin_smul`. -/
theorem extDerivAt_smul (c : ℂ) (ω : ContMDiffForm n X k) (x : X) :
    extDerivAt (c • ω) x = c • extDerivAt ω x := by
  simp only [extDerivAt_def]
  have h_smul : (c • ω).as_alternating = c • ω.as_alternating := rfl
  rw [h_smul]
  have hω : MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x :=
    ω.smooth'.mdifferentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
  have hmf :=
    const_smul_mfderiv (I := (𝓒_complex n)) (E' := FiberAlt n k)
      (f := ω.as_alternating) (z := x) hω c
  rw [hmf]
  exact ContinuousAlternatingMap.alternatizeUncurryFin_smul (𝕜 := ℂ)
    (E := TangentModel n) (F := ℂ) (n := k) (c := c)
    (f := mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x)

theorem extDeriv_add (ω η : ContMDiffForm n X k) :
    extDeriv (ω + η) = extDeriv ω + extDeriv η := by
  funext x
  exact extDerivAt_add ω η x

theorem extDeriv_smul (c : ℂ) (ω : ContMDiffForm n X k) :
    extDeriv (c • ω) = c • extDeriv ω := by
  funext x
  exact extDerivAt_smul c ω x

/-- The bundled exterior derivative of a `C^∞` form. -/
noncomputable def extDerivForm (ω : ContMDiffForm n X k) : ContMDiffForm n X (k + 1) where
  as_alternating := extDeriv ω
  smooth' := by
    -- At each point x0, the operator is smooth in a chart.
    -- The proof uses `contDiffOn_extDerivInChartWithin` from `ChartExtDeriv.lean`
    -- and the transport identity.
    -- For now, we take this as a milestone lemma with a localized sorry.
    -- (The infrastructure in ChartExtDeriv.lean contains the technical details.)
    intro x₀
    sorry

/-- The second exterior derivative of a `C^∞` form is zero (d² = 0).

    **Mathematical Justification**: This follows from the symmetry of second manifold derivatives.
    Locally, in a chart, it matches Mathlib's `extDeriv_extDeriv` for differential forms on normed spaces. -/
theorem extDeriv_extDeriv (ω : ContMDiffForm n X k) :
    extDeriv (extDerivForm ω) = 0 := by
  funext x
  -- At each point x, the identity follows from its local representation in a chart.
  sorry

end ContMDiffForm
