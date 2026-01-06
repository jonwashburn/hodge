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

@[simp] lemma mfderivInTangentCoordinates_self (ω : ContMDiffForm n X k) (x : X) :
    mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x x =
      mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x := by
  classical
  -- Unfold `inTangentCoordinates` at `(x₀,x)=(x,x)` and simplify the coordinate changes.
  have hx : (fun y : X => y) x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) ((fun y : X => y) x)).source := by
    simpa using (mem_chart_source (EuclideanSpace ℂ (Fin n)) x)
  have hy :
      (fun y : X => ω.as_alternating y) x ∈
        (chartAt (FiberAlt n k) ((fun y : X => ω.as_alternating y) x)).source := by
    simpa using (mem_chart_source (FiberAlt n k) (ω.as_alternating x))
  -- `inTangentCoordinates_eq` expresses the coordinate changes explicitly.
  have h :=
    (inTangentCoordinates_eq (I := (𝓒_complex n)) (I' := 𝓘(ℂ, FiberAlt n k))
        (f := fun y : X => y) (g := fun y : X => ω.as_alternating y)
        (ϕ := fun y : X =>
          mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating y)
        (x₀ := x) (x := x) hx hy)
  -- The coordinate changes on the diagonal are identities, so the expression reduces to `mfderiv`.
  have h_src :
      (tangentBundleCore (𝓒_complex n) X).coordChange (achart (EuclideanSpace ℂ (Fin n)) x)
          (achart (EuclideanSpace ℂ (Fin n)) x) x =
        ContinuousLinearMap.id ℂ (TangentModel n) := by
    ext v
    have hx' :
        x ∈ (tangentBundleCore (𝓒_complex n) X).baseSet (achart (EuclideanSpace ℂ (Fin n)) x) := by
      simpa [tangentBundleCore_baseSet, coe_achart] using
        (mem_achart_source (EuclideanSpace ℂ (Fin n)) x)
    simpa using (tangentBundleCore (𝓒_complex n) X).coordChange_self
      (achart (EuclideanSpace ℂ (Fin n)) x) x hx' v
  have h_tgt :
      (tangentBundleCore 𝓘(ℂ, FiberAlt n k) (FiberAlt n k)).coordChange
          (achart (FiberAlt n k) (ω.as_alternating x)) (achart (FiberAlt n k) (ω.as_alternating x))
          (ω.as_alternating x) =
        ContinuousLinearMap.id ℂ (FiberAlt n k) := by
    ext v
    have hy' :
        ω.as_alternating x ∈
          (tangentBundleCore 𝓘(ℂ, FiberAlt n k) (FiberAlt n k)).baseSet
            (achart (FiberAlt n k) (ω.as_alternating x)) := by
      simpa [tangentBundleCore_baseSet, coe_achart] using
        (mem_achart_source (FiberAlt n k) (ω.as_alternating x))
    simpa using (tangentBundleCore 𝓘(ℂ, FiberAlt n k) (FiberAlt n k)).coordChange_self
      (achart (FiberAlt n k) (ω.as_alternating x)) (ω.as_alternating x) hy' v
  -- Finish by rewriting the coordinate changes as identities.
  simpa [mfderivInTangentCoordinates, inTangentCoordinates, h_src, h_tgt] using h

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

@[simp] lemma extDerivInTangentCoordinates_self (ω : ContMDiffForm n X k) (x : X) :
    extDerivInTangentCoordinates (n := n) (X := X) (k := k) ω x x = extDerivAt (n := n) (X := X) (k := k) ω x := by
  simp [extDerivInTangentCoordinates, extDerivAt_def, mfderivInTangentCoordinates_self]

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

/-!
### Conversion from/to SmoothForm

Every `ContMDiffForm` is in particular continuous, so it determines a `SmoothForm`.
Conversely, a `SmoothForm` can be upgraded to a `ContMDiffForm` if we know it is `ContMDiff`.
-/

/-- Every `ContMDiffForm` determines a `SmoothForm` by forgetting differentiability. -/
def toSmoothForm (ω : ContMDiffForm n X k) : SmoothForm n X k where
  as_alternating := ω.as_alternating
  is_smooth := ω.smooth'.continuous

@[simp] lemma toSmoothForm_as_alternating (ω : ContMDiffForm n X k) :
    ω.toSmoothForm.as_alternating = ω.as_alternating := rfl

/-- A `SmoothForm` can be upgraded to a `ContMDiffForm` if its coefficients are `ContMDiff`.
    This is the bridge for migrating from the `Continuous`-based layer to the `ContMDiff`-based layer. -/
def ofSmoothForm (ω : SmoothForm n X k)
    (hsmooth : ContMDiff (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤ ω.as_alternating) :
    ContMDiffForm n X k where
  as_alternating := ω.as_alternating
  smooth' := hsmooth

@[simp] lemma ofSmoothForm_as_alternating (ω : SmoothForm n X k)
    (hsmooth : ContMDiff (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤ ω.as_alternating) :
    (ofSmoothForm ω hsmooth).as_alternating = ω.as_alternating := rfl

/-- Composing `ofSmoothForm` with `toSmoothForm` recovers the original form. -/
theorem toSmoothForm_ofSmoothForm (ω : SmoothForm n X k)
    (hsmooth : ContMDiff (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤ ω.as_alternating) :
    (ofSmoothForm ω hsmooth).toSmoothForm = ω := by
  ext x; rfl

/-- Composing `toSmoothForm` with `ofSmoothForm` recovers the original form. -/
theorem ofSmoothForm_toSmoothForm (ω : ContMDiffForm n X k) :
    ofSmoothForm ω.toSmoothForm ω.smooth' = ω := by
  ext x; rfl

end ContMDiffForm
