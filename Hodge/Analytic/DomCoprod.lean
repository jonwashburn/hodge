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
-/

open TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section FiniteDimensionalInstances

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {ι : Type*} [Fintype ι]

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

theorem MultilinearMap.continuous_of_finiteDimensional {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : MultilinearMap 𝕜 (fun _ : ι => E) F) :
    Continuous f := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have : f = (MultilinearMap.constOfIsEmpty 𝕜 _ (f default)) := by
      ext v; simp [Subsingleton.elim v default]
    rw [this]
    exact continuous_const
  | inr hι =>
    let n := Module.finrank 𝕜 E
    let b := Module.finBasis 𝕜 E
    have key : ∀ v, f v = ∑ r : ι → Fin n, (∏ i, b.repr (v i) (r i)) • f (fun i => b (r i)) := by
      intro v
      conv_lhs => rw [show v = (fun i => ∑ j, (b.repr (v i) j) • b j) from
        funext (fun i => (b.sum_repr (v i)).symm)]
      rw [f.map_sum]
      congr 1
      ext r
      rw [f.map_smul_univ]
    let g : (ι → E) → F := fun v =>
      ∑ r : ι → Fin n, (∏ i, b.repr (v i) (r i)) • f (fun i => b (r i))
    have hg_eq : (f : (ι → E) → F) = g := funext key
    rw [hg_eq]
    apply continuous_finset_sum
    intro r _
    apply Continuous.smul
    · apply continuous_finset_prod
      intro i _
      have : (fun v : ι → E => b.repr (v i) (r i)) =
             (fun e : E => b.repr e (r i)) ∘ (fun v : ι → E => v i) := rfl
      rw [this]
      apply Continuous.comp
      · let coordj : E →ₗ[𝕜] 𝕜 := (Finsupp.lapply (r i)).comp b.repr.toLinearMap
        exact LinearMap.continuous_of_finiteDimensional coordj
      · exact continuous_apply i
    · exact continuous_const

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

variable [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]

def domDomCongr {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (f : ContinuousAlternatingMap 𝕜 E F ι) (e : ι ≃ ι') :
    ContinuousAlternatingMap 𝕜 E F ι' where
  toAlternatingMap := f.toAlternatingMap.domDomCongr e
  cont := f.cont.comp (continuous_pi fun i => continuous_apply (e i))

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp]
theorem domDomCongr_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (f : ContinuousAlternatingMap 𝕜 E F ι) (e : ι ≃ ι') (v : ι' → E) :
    f.domDomCongr e v = f (v ∘ e) := rfl

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

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp]
theorem wedgeAlternatingTensor_add {k l : ℕ}
    (t₁ t₂ :
      TensorProduct 𝕜 (E [⋀^Fin k]→ₗ[𝕜] 𝕜) (E [⋀^Fin l]→ₗ[𝕜] 𝕜)) :
    wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) (t₁ + t₂) =
      wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) t₁ +
        wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l) t₂ := by
  classical
  ext v
  simp [wedgeAlternatingTensor, map_add]

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
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

noncomputable def wedgeAlternating {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    E [⋀^Fin (k + l)]→ₗ[𝕜] 𝕜 :=
by
  classical
  exact wedgeAlternatingTensor (𝕜 := 𝕜) (E := E) (k := k) (l := l)
    (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap)

noncomputable def wedge {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l)) :=
by
  classical
  let wedge_reindex : E [⋀^Fin (k + l)]→ₗ[𝕜] 𝕜 := wedgeAlternating (𝕜 := 𝕜) (E := E) ω η
  have h_ex :
      ∃ C : ℝ, ∀ v : Fin (k + l) → E, ‖wedge_reindex v‖ ≤ C * ∏ i, ‖v i‖ :=
    AlternatingMap.exists_bound_fin_dim (𝕜 := 𝕜) (E := E) (F := 𝕜) (ι := Fin (k + l))
      wedge_reindex
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
  simp [wedge]

theorem wedge_add_left {k l : ℕ}
    (ω₁ ω₂ : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    wedge (𝕜 := 𝕜) (E := E) (ω₁ + ω₂) η =
      wedge (𝕜 := 𝕜) (E := E) ω₁ η + wedge (𝕜 := 𝕜) (E := E) ω₂ η := by
  ext v
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
  have htensor :
      ((c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap) =
        c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) := by
      simp [TensorProduct.smul_tmul']
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
    have : c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) =
        (c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap := by
      simp [TensorProduct.smul_tmul']
    have hmove :
        (c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap =
          ω.toAlternatingMap ⊗ₜ[𝕜] (c • η.toAlternatingMap) := by
      simp [TensorProduct.smul_tmul (R := 𝕜) (R' := 𝕜) (M := (E [⋀^Fin k]→ₗ[𝕜] 𝕜))
        (N := (E [⋀^Fin l]→ₗ[𝕜] 𝕜)) c ω.toAlternatingMap η.toAlternatingMap]
    calc
      ω.toAlternatingMap ⊗ₜ[𝕜] (c • η.toAlternatingMap)
          = (c • ω.toAlternatingMap) ⊗ₜ[𝕜] η.toAlternatingMap := by
              simp [hmove]
      _ = c • (ω.toAlternatingMap ⊗ₜ[𝕜] η.toAlternatingMap) := by
              simp [this.symm]
  simp [wedge_apply, wedgeAlternating, wedgeAlternatingTensor, htensor, map_smul,
    LinearMap.compAlternatingMap_smul, AlternatingMap.domDomCongr_smul]

/-- Wedge product as a bundled bilinear continuous linear map. -/
noncomputable def wedgeCLM_alt (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (k l : ℕ) :
    (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) →L[𝕜]
      (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l) →L[𝕜]
        ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))) :=
  LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)))
    (F' := ((ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) →L[𝕜]
      (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l))))) <|
  { toFun := fun ω =>
      LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)))
        (F' := (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l)))) <|
      { toFun := fun η => wedge ω η
        map_add' := fun a b => wedge_add_right ω a b
        map_smul' := fun c a => wedge_smul_right c ω a }
    map_add' := fun a b => by ext η v; simp [wedge_add_left]
    map_smul' := fun c a => by ext η v; simp [wedge_smul_left] }

theorem continuous_wedge {k l : ℕ} :
    Continuous fun p :
        (ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k) ×
          ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) =>
        wedge (𝕜 := 𝕜) (E := E) p.1 p.2 := by
  classical
  let f := wedgeCLM_alt 𝕜 E k l
  show Continuous fun p : _ × _ => (f p.1) p.2
  admit

end ContinuousAlternatingMap

end
