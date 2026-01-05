import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Continuous Wedge Product (domCoprod)

This file is a **local overlay** used by the Hodge project.

Mathlib currently provides `AlternatingMap.domCoprod` (algebraic wedge product), but does not yet
package a corresponding `ContinuousAlternatingMap` construction in the version pinned by this repo.

This module provides the continuous version of the wedge product and its basic algebraic properties.

## Main Definitions

* `ContinuousAlternatingMap.domDomCongr`: Reindex a continuous alternating map
* `ContinuousAlternatingMap.wedge`: Wedge product for scalar-valued forms

## Main Results

* `wedge_add_left`, `wedge_add_right`: Bilinearity
* `wedge_smul_left`, `wedge_smul_right`: Scalar multiplication
* Bilinearity lemmas for `ContinuousAlternatingMap.wedge`

## Implementation Notes

The proofs use Mathlib's `AlternatingMap.domCoprod` for the algebraic structure, then
lift to `ContinuousAlternatingMap` via `AlternatingMap.mkContinuous`.

In this repo version, we construct the continuous wedge using a finite-dimensional boundedness lemma,
avoiding the explicit shuffle combinatorics needed for a sharp norm bound.

**Completed proofs**:
- `MultilinearMap.continuous_of_finiteDimensional`: Basis expansion approach
- `domDomCongr`: Reindexing continuous alternating maps
- `wedge_add_left`, `wedge_add_right`: Bilinearity via `domCoprod'` linearity
- `wedge_smul_left`, `wedge_smul_right`: Scalar multiplication via tensor product properties
- `wedge_add_left`, `wedge_add_right`, `wedge_smul_left`, `wedge_smul_right`
-/

open TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Finite-dimensionality instances (local overlay)

Mathlib provides `FiniteDimensional` instances for multilinear maps in finite dimensions, but does
not (in this pinned version) provide the corresponding instances for alternating maps and their
continuous variants.  We add these instances here so we can freely use the finite-dimensional
automation (e.g. `LinearMap.toContinuousLinearMap`) when upgrading bilinear constructions to
continuous ones.
-/

section FiniteDimensionalInstances

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {ι : Type*} [Fintype ι]

-- In finite dimensions, alternating maps form a finite-dimensional space (inject into multilinear maps).
instance instFiniteDimensional_alternatingMap
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] :
    FiniteDimensional 𝕜 (E [⋀^ι]→ₗ[𝕜] F) := by
  classical
  let f : (E [⋀^ι]→ₗ[𝕜] F) →ₗ[𝕜] MultilinearMap 𝕜 (fun _ : ι => E) F :=
    AlternatingMap.toMultilinearMapLM (R := 𝕜) (S := 𝕜) (M := E) (N := F) (ι := ι)
  have hf_inj : Function.Injective f := by
    intro a b hab
    ext v
    have : (f a : (ι → E) → F) = (f b : (ι → E) → F) := by
      simpa using
        congrArg
          (fun (g : MultilinearMap 𝕜 (fun _ : ι => E) F) => (g : (ι → E) → F))
          hab
    exact congrArg (fun g => g v) this
  exact FiniteDimensional.of_injective f hf_inj

-- In finite dimensions, continuous alternating maps form a finite-dimensional space (inject into alternating maps).
instance instFiniteDimensional_continuousAlternatingMap
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] :
    FiniteDimensional 𝕜 (E [⋀^ι]→L[𝕜] F) := by
  classical
  let f : (E [⋀^ι]→L[𝕜] F) →ₗ[𝕜] (E [⋀^ι]→ₗ[𝕜] F) :=
    ContinuousAlternatingMap.toAlternatingMapLinear (R := 𝕜) (A := 𝕜) (M := E) (N := F) (ι := ι)
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply ContinuousAlternatingMap.ext
    intro v
    have : (f a : (ι → E) → F) = (f b : (ι → E) → F) := by
      simpa using congrArg (fun (g : E [⋀^ι]→ₗ[𝕜] F) => (g : (ι → E) → F)) hab
    exact congrArg (fun g => g v) this
  exact FiniteDimensional.of_injective f hf_inj

end FiniteDimensionalInstances

/-- In finite dimensions over a complete field, any multilinear map is continuous.
    This is proved using the basis expansion: for a basis {bⱼ}, we have
    f(v₁,...,vₖ) = ∑_{j₁,...,jₖ} (∏ᵢ cᵢⱼᵢ) f(bⱼ₁,...,bⱼₖ)
    where cᵢⱼ are the coordinates of vᵢ. Since coordinates are continuous linear
    functions on a finite-dimensional space, and products/sums of continuous
    functions are continuous, f is continuous. -/
theorem MultilinearMap.continuous_of_finiteDimensional {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : MultilinearMap 𝕜 (fun _ : ι => E) F) :
    Continuous f := by
  -- Handle empty case first
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    -- Base case: ι is empty, so f is constant
    have : f = (MultilinearMap.constOfIsEmpty 𝕜 _ (f default)) := by
      ext v; simp [Subsingleton.elim v default]
    rw [this]
    exact continuous_const
  | inr hι =>
    -- Nonempty case: use basis expansion
    let n := Module.finrank 𝕜 E
    let b := Module.finBasis 𝕜 E
    -- The formula for f expressed via basis:
    -- f v = ∑_{r : ι → Fin n} (∏ i, b.repr (v i) (r i)) • f (fun i => b (r i))
    have key : ∀ v, f v = ∑ r : ι → Fin n, (∏ i, b.repr (v i) (r i)) • f (fun i => b (r i)) := by
      intro v
      conv_lhs => rw [show v = (fun i => ∑ j, (b.repr (v i) j) • b j) from
        funext (fun i => (b.sum_repr (v i)).symm)]
      rw [f.map_sum]
      congr 1
      ext r
      rw [f.map_smul_univ]
    -- Define the explicit continuous function
    let g : (ι → E) → F := fun v =>
      ∑ r : ι → Fin n, (∏ i, b.repr (v i) (r i)) • f (fun i => b (r i))
    have hg_eq : (f : (ι → E) → F) = g := funext key
    rw [hg_eq]
    -- Now show g is continuous: sum of products of continuous functions
    apply continuous_finset_sum
    intro r _
    apply Continuous.smul
    · -- Product of coordinates
      apply continuous_finset_prod
      intro i _
      -- v ↦ b.repr (v i) (r i) = (coord (r i) ∘ proj i)(v)
      have : (fun v : ι → E => b.repr (v i) (r i)) =
             (fun e : E => b.repr e (r i)) ∘ (fun v : ι → E => v i) := rfl
      rw [this]
      apply Continuous.comp
      · -- Coordinate function is continuous (linear functional in finite dim)
        let coordj : E →ₗ[𝕜] 𝕜 := (Finsupp.lapply (r i)).comp b.repr.toLinearMap
        exact LinearMap.continuous_of_finiteDimensional coordj
      · -- Projection is continuous
        exact continuous_apply i
    · exact continuous_const

/-- In finite dimensions, any alternating map has a bound. -/
theorem AlternatingMap.exists_bound_fin_dim {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : E [⋀^ι]→ₗ[𝕜] F) :
    ∃ C : ℝ, ∀ v : ι → E, ‖f v‖ ≤ C * ∏ i, ‖v i‖ := by
  let f_multi := f.toMultilinearMap
  have hcont : Continuous f_multi := MultilinearMap.continuous_of_finiteDimensional f_multi
  obtain ⟨C, _, hC⟩ := f_multi.exists_bound_of_continuous hcont
  exact ⟨C, hC⟩

noncomputable section

namespace ContinuousAlternatingMap

-- For the continuity proofs below we use that multilinear/alternating maps are continuous in
-- finite-dimensional normed spaces over a complete field.
variable [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]

/-! ## Domain reindexing for ContinuousAlternatingMap -/

/-- Reindex the domain of a continuous alternating map along an equivalence.
    If `f : E [⋀^ι]→L[𝕜] F` and `e : ι ≃ ι'`, then `f.domDomCongr e : E [⋀^ι']→L[𝕜] F`.
    We have `(f.domDomCongr e) v = f (v ∘ e)`. -/
def domDomCongr {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (f : ContinuousAlternatingMap 𝕜 E F ι) (e : ι ≃ ι') :
    ContinuousAlternatingMap 𝕜 E F ι' where
  toAlternatingMap := f.toAlternatingMap.domDomCongr e
  cont := f.cont.comp (continuous_pi fun i => continuous_apply (e i))

@[simp]
theorem domDomCongr_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (f : ContinuousAlternatingMap 𝕜 E F ι) (e : ι ≃ ι') (v : ι' → E) :
    f.domDomCongr e v = f (v ∘ e) := rfl

/-! ## Scalar-valued wedge product -/

/-- The (algebraic) wedge construction as a function of an *arbitrary* tensor input.

We keep the tensor input explicit to avoid definitional unfolding of `domCoprod'` on pure tensors
in later proofs (which would expand into shuffle sums). -/
noncomputable def wedgeAlternatingTensor {k l : ℕ}
    (t :
      TensorProduct 𝕜 (E [⋀^Fin k]→ₗ[𝕜] 𝕜) (E [⋀^Fin l]→ₗ[𝕜] 𝕜)) :
    E [⋀^Fin (k + l)]→ₗ[𝕜] 𝕜 :=
by
  classical
  let wedge_tensor :
      E [⋀^Fin k ⊕ Fin l]→ₗ[𝕜] (TensorProduct 𝕜 𝕜 𝕜) :=
    AlternatingMap.domCoprod' (ιa := Fin k) (ιb := Fin l)
      (R' := 𝕜) (Mᵢ := E) (N₁ := 𝕜) (N₂ := 𝕜) t
  let wedge_scalar : E [⋀^Fin k ⊕ Fin l]→ₗ[𝕜] 𝕜 :=
    (LinearMap.mul' 𝕜 𝕜).compAlternatingMap wedge_tensor
  exact wedge_scalar.domDomCongr finSumFinEquiv

@[simp]
theorem wedgeAlternatingTensor_add {k l : ℕ}
    (t₁ t₂ :
      TensorProduct 𝕜 (E [⋀^Fin k]→ₗ[𝕜] 𝕜) (E [⋀^Fin l]→ₗ[𝕜] 𝕜)) :
    wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) (t₁ + t₂) =
      wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) t₁ +
        wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) t₂ := by
  classical
  -- `domCoprod'` is linear in the tensor input; the remaining steps are linear as well.
  ext v
  simp [wedgeAlternatingTensor, map_add]

@[simp]
theorem wedgeAlternatingTensor_smul {k l : ℕ} (c : 𝕜)
    (t :
      TensorProduct 𝕜 (E [⋀^Fin k]→ₗ[𝕜] 𝕜) (E [⋀^Fin l]→ₗ[𝕜] 𝕜)) :
    wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) (c • t) =
      c • wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) t := by
  classical
  ext v
  simp [wedgeAlternatingTensor, map_smul, LinearMap.compAlternatingMap_smul,
    AlternatingMap.domDomCongr_smul]

/-- The underlying *algebraic* alternating map of the wedge product.

This is the `AlternatingMap` obtained by `domCoprod'` (tensor-valued), composition with scalar
multiplication, and reindexing along `finSumFinEquiv`. -/
noncomputable def wedgeAlternating {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    E [⋀^Fin (k + l)]→ₗ[𝕜] 𝕜 :=
by
  classical
  exact wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l)
    (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap)

/-- The wedge product of scalar-valued continuous alternating maps.
    Given ω : E [⋀^Fin k]→L[𝕜] 𝕜 and η : E [⋀^Fin l]→L[𝕜] 𝕜,
    produces ω ∧ η : E [⋀^Fin (k+l)]→L[𝕜] 𝕜. -/
noncomputable def wedge {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l)) :=
by
  classical
  let wedge_reindex : E [⋀^Fin (k + l)]→ₗ[𝕜] 𝕜 := wedgeAlternating (𝕜 := 𝕜) (E := E) ω η
  -- Step 4: continuity from finite-dimensional boundedness
  have h_ex :
      ∃ C : ℝ, ∀ v : Fin (k + l) → E, ‖wedge_reindex v‖ ≤ C * ∏ i, ‖v i‖ :=
    AlternatingMap.exists_bound_fin_dim (𝕜 := 𝕜) (E := E) (F := 𝕜) (ι := Fin (k + l))
      wedge_reindex
  classical
  let C : ℝ := Classical.choose h_ex
  have hC : ∀ v : Fin (k + l) → E, ‖wedge_reindex v‖ ≤ C * ∏ i, ‖v i‖ :=
    Classical.choose_spec h_ex
  exact wedge_reindex.mkContinuous C hC

@[simp] theorem wedge_apply {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l))
    (v : Fin (k + l) → E) :
    (wedge (𝕜 := 𝕜) (E := E) ω η) v =
      (wedgeAlternating (𝕜 := 𝕜) (E := E) ω η) v := by
  -- `wedge` is `mkContinuous` on the underlying alternating map.
  simp [wedge]

/-! ### Bilinearity -/

theorem wedge_add_left {k l : ℕ}
    (ω₁ ω₂ : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    wedge (𝕜 := 𝕜) (E := E) (ω₁ + ω₂) η =
      wedge (𝕜 := 𝕜) (E := E) ω₁ η + wedge (𝕜 := 𝕜) (E := E) ω₂ η := by
  ext v
  -- Avoid expanding `domCoprod` into shuffle sums: the additivity happens at the tensor level.
  simp [wedge_apply, wedgeAlternating, TensorProduct.add_tmul]

theorem wedge_add_right {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η₁ η₂ : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    wedge (𝕜 := 𝕜) (E := E) ω (η₁ + η₂) =
      wedge (𝕜 := 𝕜) (E := E) ω η₁ + wedge (𝕜 := 𝕜) (E := E) ω η₂ := by
  ext v
  simp [wedge_apply, wedgeAlternating, TensorProduct.tmul_add]

theorem wedge_smul_left {k l : ℕ} (c : 𝕜)
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    wedge (𝕜 := 𝕜) (E := E) (c • ω) η = c • wedge (𝕜 := 𝕜) (E := E) ω η := by
  ext v
  -- Avoid expanding `domCoprod'` into shuffle sums: work at the tensor level.
  have htensor :
      ((c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap) =
        c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) := by
    -- scalar multiplication on tensor products acts on pure tensors by scaling the left factor
    have : c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) =
        (c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap := by
      simp [TensorProduct.smul_tmul']
    simpa using this.symm
  simp [wedge_apply, wedgeAlternating, wedgeAlternatingTensor, htensor, map_smul,
    LinearMap.compAlternatingMap_smul, AlternatingMap.domDomCongr_smul]

theorem wedge_smul_right {k l : ℕ} (c : 𝕜)
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    wedge (𝕜 := 𝕜) (E := E) ω (c • η) = c • wedge (𝕜 := 𝕜) (E := E) ω η := by
  ext v
  have htensor :
      (ω.toAlternatingMap ⊗ₜ[𝕜] (c • η.toAlternatingMap)) =
        c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) := by
    -- scalar multiplication on tensor products can be moved to the left factor, hence pulled out
    have : c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) =
        (c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap := by
      simp [TensorProduct.smul_tmul']
    -- move the scalar to the right factor
    have hmove :
        (c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap =
          ω.toAlternatingMap ⊗ₜ[𝕜] (c • η.toAlternatingMap) := by
      -- `smul_tmul` moves the scalar between tensor factors over a commutative base ring
      simpa using (TensorProduct.smul_tmul (R := 𝕜) (R' := 𝕜) (M := (E [⋀^Fin k]→ₗ[𝕜] 𝕜))
        (N := (E [⋀^Fin l]→ₗ[𝕜] 𝕜)) c ω.toAlternatingMap η.toAlternatingMap)
    -- combine
    calc
      ω.toAlternatingMap ⊗ₜ[𝕜] (c • η.toAlternatingMap)
          = (c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap := by
              simpa [hmove] using hmove.symm
      _ = c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) := by
              simpa using this.symm
  simp [wedge_apply, wedgeAlternating, wedgeAlternatingTensor, htensor, map_smul,
    LinearMap.compAlternatingMap_smul, AlternatingMap.domDomCongr_smul]

/-! ### Continuity in both arguments -/

theorem continuous_wedge {k l : ℕ} :
    Continuous fun p :
        (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k) ×
          ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) =>
        wedge (𝕜 := 𝕜) (E := E) p.1 p.2 := by
  classical
  -- Package `wedge` as a bilinear map `ω →ₗ η →ₗ ω ∧ η`.
  let wedgeₗ :
      (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) →ₗ[𝕜]
        (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) →ₗ[𝕜]
          (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))) :=
    LinearMap.mk₂ 𝕜
      (fun ω η => wedge (𝕜 := 𝕜) (E := E) ω η)
      (fun ω₁ ω₂ η => by
        simpa [wedge_add_left (𝕜 := 𝕜) (E := E) ω₁ ω₂ η] )
      (fun c ω η => by
        simpa [wedge_smul_left (𝕜 := 𝕜) (E := E) c ω η])
      (fun ω η₁ η₂ => by
        simpa [wedge_add_right (𝕜 := 𝕜) (E := E) ω η₁ η₂])
      (fun c ω η => by
        simpa [wedge_smul_right (𝕜 := 𝕜) (E := E) c ω η])

  -- Upgrade the inner linear maps in `η` to continuous linear maps (finite-dimensional domain).
  let eη :
      ((ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l) →ₗ[𝕜]
          ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))) ≃ₗ[𝕜]
        (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l) →L[𝕜]
          ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l)))) :=
    LinearMap.toContinuousLinearMap (𝕜 := 𝕜)
      (E := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l))
      (F' := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l)))

  let wedgeₗ' :
      (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) →ₗ[𝕜]
        (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l) →L[𝕜]
          ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))) :=
    (eη : _ →ₗ[𝕜] _).comp wedgeₗ

  -- Upgrade the outer linear map in `ω` to a continuous linear map (finite-dimensional domain).
  let wedgeCLM :
      (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) →L[𝕜]
        (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l) →L[𝕜]
          ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))) :=
    (LinearMap.toContinuousLinearMap (𝕜 := 𝕜)
      (E := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
      (F' := (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l) →L[𝕜]
        ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))))) wedgeₗ'

  -- Joint continuity of `fun (ω,η) => wedgeCLM ω η` (reduce to the multilinear evaluation lemma).
  simpa [wedgeCLM, wedgeₗ', wedgeₗ] using (by
    -- generic lemma: for `f : G →L (E →L F)`, the uncurried map is continuous
    have :
        Continuous fun p :
            (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k) ×
              ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) =>
            wedgeCLM p.1 p.2 := by
      -- proof via `ContinuousLinearMap.continuous_uncurry_of_multilinear` on `Unit`
      -- (see `prove_continuous_uncurry_of_clm_via_multilinear2.lean` scratch)
      let eIso :
          (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l) →L[𝕜]
              ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))) ≃L[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Unit =>
              ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l))
              (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))) :=
        (ContinuousMultilinearMap.ofSubsingletonₗᵢ
            (𝕜 := 𝕜) (ι := Unit)
            (G := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l))
            (G' := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l)))
            (i := ())).toContinuousLinearEquiv
      let f' :
          (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) →L[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Unit =>
              ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l))
              (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))) :=
        (eIso.toContinuousLinearMap).comp wedgeCLM
      have hf' :
          Continuous fun q :
              (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k) ×
                (Unit → ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l))) =>
              f' q.1 q.2 := f'.continuous_uncurry_of_multilinear
      have hconst :
          Continuous fun q :
              (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k) ×
                ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) =>
              (q.1, (fun _ : Unit => q.2)) := by
        fun_prop
      -- Compose and simplify.
      simpa [f', eIso] using (hf'.comp hconst)
    -- turn back into the desired statement
    simpa using this)

end ContinuousAlternatingMap

end
