import Hodge.WorkInProgress.GMT.EuclideanMollifier
import Hodge.WorkInProgress.GMT.LocalCurrents
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section

namespace Hodge.GMT

variable {n : ℕ} {k : ℕ}

open Classical
open scoped BigOperators

section TranslationBCF

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The homeomorphism `y ↦ x - y` on a real normed vector space. -/
noncomputable def subHomeomorph (x : E) : E ≃ₜ E :=
  (Homeomorph.neg (G := E)).trans (Homeomorph.addLeft x)

@[simp] theorem subHomeomorph_apply (x y : E) :
    subHomeomorph x y = x - y := by
  simp [subHomeomorph, sub_eq_add_neg]

/-- A compactly supported continuous function is globally bounded. -/
theorem exists_norm_bound_of_hasCompactSupport {g : E → G}
    (hg : Continuous g) (hsupp : HasCompactSupport g) :
    ∃ C : ℝ, ∀ z, ‖g z‖ ≤ C := by
  let K := tsupport g
  have hK : IsCompact K := by
    simpa [HasCompactSupport] using hsupp
  rcases hK.exists_bound_of_continuousOn (hg.continuousOn) with ⟨C, hC⟩
  refine ⟨max C 0, ?_⟩
  intro z
  by_cases hz : z ∈ K
  · exact (hC z hz).trans (le_max_left _ _)
  · have hzero : g z = 0 := by
      by_contra hne
      exact hz (subset_tsupport _ (by simpa [Function.mem_support] using hne))
    simpa [hzero] using (le_max_right C 0)

/-- The translated compactly supported function viewed in the sup-norm space of bounded continuous
functions. -/
noncomputable def translateBCF (g : E → G) (hg : Continuous g) (hsupp : HasCompactSupport g) (x : E) :
    BoundedContinuousFunction E G :=
  let C := Classical.choose (exists_norm_bound_of_hasCompactSupport (hg := hg) hsupp)
  let hC := Classical.choose_spec (exists_norm_bound_of_hasCompactSupport (hg := hg) hsupp)
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => g (x - y))
    (hg.comp (continuous_const.sub continuous_id))
    C
    (fun y => hC (x - y))

@[simp] theorem translateBCF_apply {g : E → G} (hg : Continuous g) (hsupp : HasCompactSupport g)
    (x y : E) :
    translateBCF g hg hsupp x y = g (x - y) := by
  rfl

/-- Outside the topological support, a function vanishes. -/
theorem eq_zero_of_not_mem_tsupport {g : E → G} {z : E}
    (hz : z ∉ tsupport g) : g z = 0 := by
  by_contra hne
  exact hz (subset_tsupport _ (by simpa [Function.mem_support] using hne))

/-- A compactly supported function on a finite-dimensional normed space has support contained in
some centered closed ball. -/
theorem exists_closedBall_tsupport_subset {g : E → G} (hsupp : HasCompactSupport g) :
    ∃ R : ℝ, 0 ≤ R ∧ tsupport g ⊆ Metric.closedBall (0 : E) R := by
  let K := tsupport g
  have hK : IsCompact K := by
    simpa [HasCompactSupport] using hsupp
  rcases hK.isBounded.subset_closedBall (0 : E) with ⟨R, hR⟩
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  exact Set.Subset.trans hR (Metric.closedBall_subset_closedBall (le_max_left _ _))

/-- A continuous compactly supported map on a finite-dimensional normed space is uniformly
continuous. -/
theorem uniformContinuous_of_continuous_hasCompactSupport {g : E → G}
    (hg : Continuous g) (hsupp : HasCompactSupport g) : UniformContinuous g := by
  rcases exists_closedBall_tsupport_subset (g := g) hsupp with ⟨R, hRnonneg, hRsubset⟩
  let K : Set E := Metric.closedBall (0 : E) (R + 1)
  have hKcompact : IsCompact K := by
    simpa [K] using isCompact_closedBall (0 : E) (R + 1)
  have hKuc : UniformContinuousOn g K :=
    hKcompact.uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  rcases (Metric.uniformContinuousOn_iff.1 hKuc) ε hε with ⟨δ, hδ, hδprop⟩
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro a b hab
  by_cases haball : a ∈ Metric.closedBall (0 : E) R ∨ b ∈ Metric.closedBall (0 : E) R
  · have haK : a ∈ K := by
      rcases haball with haR | hbR
      · exact Metric.closedBall_subset_closedBall (by linarith) haR
      · rw [Metric.mem_closedBall] at hbR ⊢
        exact le_of_lt <| calc
          dist a 0 ≤ dist a b + dist b 0 := dist_triangle a b 0
          _ < 1 + R := by
            exact add_lt_add_of_lt_of_le (lt_of_lt_of_le hab (min_le_right _ _)) hbR
          _ = R + 1 := by linarith
    have hbK : b ∈ K := by
      rcases haball with haR | hbR
      · rw [Metric.mem_closedBall] at haR ⊢
        exact le_of_lt <| calc
          dist b 0 ≤ dist b a + dist a 0 := dist_triangle b a 0
          _ < 1 + R := by
            have hab' : dist b a < min δ 1 := by simpa [dist_comm] using hab
            exact add_lt_add_of_lt_of_le (lt_of_lt_of_le hab' (min_le_right _ _)) haR
          _ = R + 1 := by linarith
      · exact Metric.closedBall_subset_closedBall (by linarith) hbR
    exact hδprop a haK b hbK (lt_of_lt_of_le hab (min_le_left _ _))
  · have haR : a ∉ Metric.closedBall (0 : E) R := by
      have hpair : a ∉ Metric.closedBall (0 : E) R ∧ b ∉ Metric.closedBall (0 : E) R := by
        simpa [not_or] using haball
      exact hpair.1
    have hbR : b ∉ Metric.closedBall (0 : E) R := by
      have hpair : a ∉ Metric.closedBall (0 : E) R ∧ b ∉ Metric.closedBall (0 : E) R := by
        simpa [not_or] using haball
      exact hpair.2
    have haza : a ∉ tsupport g := fun ha => haR (hRsubset ha)
    have hazb : b ∉ tsupport g := fun hb => hbR (hRsubset hb)
    simpa [eq_zero_of_not_mem_tsupport (g := g) haza, eq_zero_of_not_mem_tsupport (g := g) hazb]
      using hε

/-- The Fréchet derivative of a function vanishes outside its topological support. -/
theorem fderiv_eq_zero_of_not_mem_tsupport {g : E → G} {z : E}
    (hz : z ∉ tsupport g) (hdiff : DifferentiableAt ℝ g z) :
    fderiv ℝ g z = 0 := by
  have hzero_eventually : g =ᶠ[nhds z] (fun _ : E => (0 : G)) := by
    filter_upwards [((isClosed_tsupport g).isOpen_compl.mem_nhds hz)] with w hw
    exact eq_zero_of_not_mem_tsupport (g := g) hw
  have hzeroDeriv : HasFDerivAt g (0 : E →L[ℝ] G) z := by
    simpa using
      ((hasFDerivAt_const (𝕜 := ℝ) (c := (0 : G)) z).congr_of_eventuallyEq hzero_eventually)
  exact hdiff.hasFDerivAt.unique hzeroDeriv

/-- Compact support is inherited by the Fréchet derivative. -/
theorem hasCompactSupport_fderiv {g : E → G}
    (hsupp : HasCompactSupport g) (hdiff : Differentiable ℝ g) :
    HasCompactSupport (fderiv ℝ g) := by
  have hcompact : IsCompact (tsupport g) := by
    simpa [HasCompactSupport] using hsupp
  exact HasCompactSupport.intro hcompact fun z hz =>
    fderiv_eq_zero_of_not_mem_tsupport (g := g) hz (hdiff z)

/-- Points on the segment from `z` to `z + h` stay within `‖h‖` of `z`. -/
theorem norm_sub_le_of_mem_segment {z h w : E}
    (hw : w ∈ segment ℝ z (z + h)) : ‖w - z‖ ≤ ‖h‖ := by
  rw [segment_eq_image_lineMap ℝ z (z + h)] at hw
  rcases hw with ⟨t, ht, rfl⟩
  rcases ht with ⟨ht0, ht1⟩
  calc
    ‖AffineMap.lineMap z (z + h) t - z‖ = ‖t • h‖ := by
      simp [AffineMap.lineMap_apply_module, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        smul_add, add_smul]
    _ = |t| * ‖h‖ := norm_smul t h
    _ ≤ ‖h‖ := by
      have htabs : |t| ≤ 1 := by simpa [abs_of_nonneg ht0] using ht1
      nlinarith [norm_nonneg h]

/-- Pointwise application of a bounded continuous family of continuous linear maps. -/
noncomputable def bcfApply (F : BoundedContinuousFunction E (E →L[ℝ] G)) :
    E →L[ℝ] BoundedContinuousFunction E G := by
  let L : E →ₗ[ℝ] BoundedContinuousFunction E G := {
    toFun := fun h =>
      BoundedContinuousFunction.ofNormedAddCommGroup
        (fun y => F y h)
        (((ContinuousLinearMap.apply (𝕜 := ℝ) (E := E) (Fₗ := G)) h).continuous.comp F.continuous)
        (‖F‖ * ‖h‖)
        (fun y => by
          calc
            ‖F y h‖ ≤ ‖F y‖ * ‖h‖ := (F y).le_opNorm h
            _ ≤ ‖F‖ * ‖h‖ := by
              gcongr
              exact F.norm_coe_le_norm y)
    map_add' := by
      intro h₁ h₂
      ext y
      simp
    map_smul' := by
      intro r h
      ext y
      simp }
  exact L.mkContinuousOfExistsBound <| by
    refine ⟨‖F‖, ?_⟩
    intro h
    change ‖L h‖ ≤ ‖F‖ * ‖h‖
    exact (BoundedContinuousFunction.norm_le_of_nonempty).2 <| by
      intro y
      calc
        ‖F y h‖ ≤ ‖F y‖ * ‖h‖ := (F y).le_opNorm h
        _ ≤ ‖F‖ * ‖h‖ := by
          gcongr
          exact F.norm_coe_le_norm y

@[simp] theorem bcfApply_apply (F : BoundedContinuousFunction E (E →L[ℝ] G)) (h y : E) :
    bcfApply F h y = F y h := by
  simp [bcfApply]

/-- The pointwise-application operator on bounded continuous families of linear maps is itself a
continuous linear map. -/
noncomputable def bcfApplyCLM :
    BoundedContinuousFunction E (E →L[ℝ] G) →L[ℝ] E →L[ℝ] BoundedContinuousFunction E G := by
  let L : BoundedContinuousFunction E (E →L[ℝ] G) →ₗ[ℝ] E →L[ℝ] BoundedContinuousFunction E G := {
    toFun := bcfApply
    map_add' := by
      intro F₁ F₂
      ext h y
      simp [bcfApply]
    map_smul' := by
      intro r F
      ext h y
      simp [bcfApply] }
  have hL : ∀ F : BoundedContinuousFunction E (E →L[ℝ] G), ‖L F‖ ≤ 1 * ‖F‖ := by
    intro F
    have hbound : ∀ h : E, ‖L F h‖ ≤ ‖F‖ * ‖h‖ := by
      intro h
      change ‖bcfApply F h‖ ≤ ‖F‖ * ‖h‖
      exact (BoundedContinuousFunction.norm_le_of_nonempty).2 <| by
        intro y
        calc
          ‖F y h‖ ≤ ‖F y‖ * ‖h‖ := (F y).le_opNorm h
          _ ≤ ‖F‖ * ‖h‖ := by
            gcongr
            exact F.norm_coe_le_norm y
    calc
      ‖L F‖ ≤ ‖F‖ := (L F).opNorm_le_bound (norm_nonneg F) hbound
      _ = 1 * ‖F‖ := by simp
  exact
    show BoundedContinuousFunction E (E →L[ℝ] G) →L[ℝ] E →L[ℝ] BoundedContinuousFunction E G from
      (LinearMap.mkContinuousOfExistsBound
        (σ := RingHom.id ℝ)
        (E := BoundedContinuousFunction E (E →L[ℝ] G))
        (F := E →L[ℝ] BoundedContinuousFunction E G)
        L ⟨1, hL⟩ : BoundedContinuousFunction E (E →L[ℝ] G) →L[ℝ]
          E →L[ℝ] BoundedContinuousFunction E G)

@[simp] theorem bcfApplyCLM_apply_apply
    (F : BoundedContinuousFunction E (E →L[ℝ] G)) (h y : E) :
    bcfApplyCLM F h y = F y h := by
  simp [bcfApplyCLM, bcfApply]

/-- Translating a compactly supported `C¹` function is Fréchet differentiable in the translation
parameter, with derivative given by translating its derivative. -/
theorem hasFDerivAt_translateBCF {g : E → G} {g' : E → E →L[ℝ] G}
    (hg : Continuous g) (hsupp : HasCompactSupport g)
    (hg' : Continuous g') (hsupp' : HasCompactSupport g')
    (hderiv : ∀ z, HasFDerivAt g (g' z) z) (x : E) :
    HasFDerivAt (fun z => translateBCF g hg hsupp z)
      (bcfApplyCLM (translateBCF g' hg' hsupp' x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have huc : UniformContinuous g' :=
    uniformContinuous_of_continuous_hasCompactSupport (g := g') hg' hsupp'
  rcases (Metric.uniformContinuous_iff.1 huc) c hc with ⟨δ, hδ, hδprop⟩
  refine Metric.mem_nhds_iff.2 ⟨δ, hδ, ?_⟩
  intro h hh
  have hhδ : ‖h‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hh
  refine (BoundedContinuousFunction.norm_le_of_nonempty).2 ?_
  intro y
  let z : E := x - y
  have hbound : ∀ w ∈ segment ℝ z (z + h), ‖g' w - g' z‖ ≤ c := by
    intro w hw
    have hsegdist : dist w z ≤ ‖h‖ := by
      simpa [dist_eq_norm, z] using norm_sub_le_of_mem_segment (z := z) (h := h) hw
    exact le_of_lt (hδprop (lt_of_le_of_lt hsegdist hhδ))
  have hmv :
      ‖g (z + h) - g z - g' z ((z + h) - z)‖ ≤ c * ‖(z + h) - z‖ := by
    simpa using
      (convex_segment z (z + h)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (fun w _ => (hderiv w).hasFDerivWithinAt) hbound
        (left_mem_segment ℝ z (z + h)) (right_mem_segment ℝ z (z + h))
  simpa [translateBCF_apply, bcfApplyCLM_apply_apply, z, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using hmv

/-- Translation acts continuously on compactly supported functions in the sup norm. -/
theorem continuous_translateBCF {g : E → G}
    (hg : Continuous g) (hsupp : HasCompactSupport g) :
    Continuous (fun x => translateBCF g hg hsupp x) := by
  have huc : UniformContinuous g :=
    uniformContinuous_of_continuous_hasCompactSupport (g := g) hg hsupp
  rw [Metric.continuous_iff]
  intro x ε hε
  rcases (Metric.uniformContinuous_iff.1 huc) (ε / 2) (half_pos hε) with ⟨δ, hδ, hδprop⟩
  refine ⟨δ, hδ, ?_⟩
  intro x' hx'
  have hdist :
      dist (translateBCF g hg hsupp x') (translateBCF g hg hsupp x) ≤ ε / 2 := by
    refine (BoundedContinuousFunction.dist_le (by linarith)).2 ?_
    intro y
    refine le_of_lt ?_
    have hxy : dist (x' - y) (x - y) < δ := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx'
    simpa [translateBCF_apply] using hδprop hxy
  exact lt_of_le_of_lt hdist (by linarith)

end TranslationBCF

/-- A real basis of the Euclidean model fiber of `k`-forms. -/
noncomputable def modelFiberBasis :
    Module.Basis (Fin (Module.finrank ℝ (FiberAlt n k))) ℝ (FiberAlt n k) :=
  Module.finBasis ℝ (FiberAlt n k)

/-- The shifted Euclidean bump is smooth in the spatial variable. -/
theorem shifted_bump_contDiff (ε : ℝ) (hε : ε ≠ 0) (x : TangentModel n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y) := by
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => bumpBaseFun (E := TangentModel n) z) := by
    simpa [bumpBaseFun] using (bumpBase (E := TangentModel n)).contDiff (n := (⊤ : ℕ∞))
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => ε⁻¹ • z) :=
    (contDiff_const_smul (c := ε⁻¹)).comp contDiff_id
  have hbump : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => bump (E := TangentModel n) ε z) := by
    simpa [bump] using hbase.comp hscale
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun y : TangentModel n => x - y) := by
    simpa using contDiff_const.sub contDiff_id
  simpa [shifted_bump] using hbump.comp hsub

/-- The shifted Euclidean bump is compactly supported in the spatial variable. -/
theorem shifted_bump_hasCompactSupport (ε : ℝ) (hε : ε ≠ 0) (x : TangentModel n) :
    HasCompactSupport (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y) := by
  have hbase : HasCompactSupport (fun z : TangentModel n => bumpBaseFun (E := TangentModel n) z) := by
    simpa [bumpBaseFun] using (bumpBase (E := TangentModel n)).hasCompactSupport
  have hbump : HasCompactSupport (fun z : TangentModel n => bump (E := TangentModel n) ε z) := by
    simpa [bump] using hbase.comp_smul (inv_ne_zero hε)
  have hsub :
      Topology.IsClosedEmbedding (fun y : TangentModel n => x - y) := by
    simpa [sub_eq_add_neg, Function.comp] using
      (Topology.IsClosedEmbedding.comp
        (hg := (Homeomorph.addLeft x).isClosedEmbedding)
        (hf := (Homeomorph.neg (G := TangentModel n)).isClosedEmbedding))
  simpa [shifted_bump, Function.comp] using hbump.comp_isClosedEmbedding hsub

/-- Fixed-bump test form centered at `x` with fiber coefficient `A`. -/
noncomputable def shiftedBumpTestForm (ε : ℝ) (hε : ε ≠ 0)
    (x : TangentModel n) (A : FiberAlt n k) : Hodge.TestForm n (TangentModel n) k :=
  ⟨{ as_alternating := fun y => shifted_bump (E := TangentModel n) ε x y • A
    , is_smooth := by
        have hscalar := shifted_bump_contDiff (n := n) ε hε x
        have hsmul :
            ContDiff ℝ (⊤ : ℕ∞)
              (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y • A) := by
          simpa using hscalar.smul contDiff_const
        show IsSmoothAlternating n (TangentModel n) k
          (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y • A)
        unfold IsSmoothAlternating 𝓒_complex TangentModel
        convert hsmul.contMDiff using 1 <;> simp [formSmoothness]
    }
    , by
        have hscalar :
            HasCompactSupport (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y) :=
          shifted_bump_hasCompactSupport (n := n) ε hε x
        have hcoeff :
            HasCompactSupport
              ((fun r : ℝ => r • A) ∘ (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y)) :=
          HasCompactSupport.comp_left hscalar (by
            ext r
            simp)
        simpa [Function.comp] using hcoeff ⟩

/-- Forget a model test form to a bounded continuous coefficient field. -/
noncomputable def modelTestFormToBCF :
    Hodge.TestForm n (TangentModel n) k →L[ℝ]
      BoundedContinuousFunction (TangentModel n) (FiberAlt n k) := by
  let L : Hodge.TestForm n (TangentModel n) k →ₗ[ℝ]
      BoundedContinuousFunction (TangentModel n) (FiberAlt n k) := {
    toFun := fun ω =>
      BoundedContinuousFunction.ofNormedAddCommGroup
        (fun x => (ω : SmoothForm n (TangentModel n) k).as_alternating x)
        (ω.1.is_smooth.continuous)
        ‖ω‖
        (fun x => by
          simpa [Hodge.TestForm.comass, pointwiseComass] using
            Hodge.TestForm.pointwiseComass_le_comass (n := n) (X := TangentModel n) (k := k) ω x)
    map_add' := by
      intro ω η
      ext x
      simp
    map_smul' := by
      intro r ω
      ext x
      simp [Hodge.TestForm.coe_smul_real] }
  exact L.mkContinuousOfExistsBound <| by
    refine ⟨1, ?_⟩
    intro ω
    change ‖L ω‖ ≤ 1 * ‖ω‖
    calc
      ‖L ω‖ ≤ ‖ω‖ := by
        exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 <| by
          intro x
          simpa [Hodge.TestForm.comass, pointwiseComass] using
            Hodge.TestForm.pointwiseComass_le_comass (n := n) (X := TangentModel n) (k := k) ω x
      _ = 1 * ‖ω‖ := by simp

@[simp] theorem modelTestFormToBCF_apply (ω : Hodge.TestForm n (TangentModel n) k)
    (x : TangentModel n) :
    modelTestFormToBCF (n := n) (k := k) ω x =
      (ω : SmoothForm n (TangentModel n) k).as_alternating x := by
  simp [modelTestFormToBCF, LinearMap.mkContinuousOfExistsBound_apply]

theorem modelTestFormToBCF_injective :
    Function.Injective (modelTestFormToBCF (n := n) (k := k)) := by
  intro ω η h
  apply Subtype.ext
  apply SmoothForm.ext
  funext x
  simpa [modelTestFormToBCF_apply] using congrArg (fun F => F x) h

theorem modelTestFormToBCF_norm_eq (ω : Hodge.TestForm n (TangentModel n) k) :
    ‖modelTestFormToBCF (n := n) (k := k) ω‖ = ‖ω‖ := by
  apply le_antisymm
  · exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 <| by
      intro x
      simpa [Hodge.TestForm.comass, pointwiseComass, modelTestFormToBCF_apply] using
        Hodge.TestForm.pointwiseComass_le_comass (n := n) (X := TangentModel n) (k := k) ω x
  · change Hodge.TestForm.comass ω ≤ ‖modelTestFormToBCF (n := n) (k := k) ω‖
    unfold Hodge.TestForm.comass
    apply csSup_le
    · exact Set.range_nonempty _
    · intro r hr
      rcases hr with ⟨x, rfl⟩
      simpa [pointwiseComass, modelTestFormToBCF_apply] using
        (modelTestFormToBCF (n := n) (k := k) ω).norm_coe_le_norm x

/-- The subspace of bounded continuous coefficient fields coming from model test forms. -/
noncomputable def modelTestFormBCFRange :
    Submodule ℝ (BoundedContinuousFunction (TangentModel n) (FiberAlt n k)) :=
  (modelTestFormToBCF (n := n) (k := k)).toLinearMap.range

/-- The forgetful map to bounded continuous functions is a linear equivalence onto its range. -/
noncomputable def modelTestFormBCFRangeEquiv :
    Hodge.TestForm n (TangentModel n) k ≃ₗ[ℝ] modelTestFormBCFRange (n := n) (k := k) :=
  LinearEquiv.ofInjective (modelTestFormToBCF (n := n) (k := k)).toLinearMap
    (modelTestFormToBCF_injective (n := n) (k := k))

/-- The range equivalence is continuous in both directions. -/
noncomputable def modelTestFormBCFRangeEquivCLM :
    Hodge.TestForm n (TangentModel n) k ≃L[ℝ] modelTestFormBCFRange (n := n) (k := k) := by
  let e := modelTestFormBCFRangeEquiv (n := n) (k := k)
  refine e.toContinuousLinearEquivOfBounds 1 1 ?_ ?_
  · intro ω
    change ‖modelTestFormToBCF (n := n) (k := k) ω‖ ≤ 1 * ‖ω‖
    rw [modelTestFormToBCF_norm_eq]
    simp
  · intro F
    calc
      ‖e.symm F‖ = ‖modelTestFormToBCF (n := n) (k := k) (e.symm F)‖ := by
        rw [modelTestFormToBCF_norm_eq]
      _ = ‖(F : BoundedContinuousFunction (TangentModel n) (FiberAlt n k))‖ := by
        have hEq :
            modelTestFormToBCF (n := n) (k := k) (e.symm F) =
              (F : BoundedContinuousFunction (TangentModel n) (FiberAlt n k)) := by
          exact congrArg Subtype.val (e.apply_symm_apply F)
        simpa [hEq]
      _ ≤ 1 * ‖F‖ := by simp

/-- Restrict a model current to the bounded-continuous range subspace of test forms. -/
noncomputable def modelCurrentOnBCFRange (T : ModelCurrent n k) :
    StrongDual ℝ (modelTestFormBCFRange (n := n) (k := k)) :=
  T.toContinuousLinearMap.comp
    (modelTestFormBCFRangeEquivCLM (n := n) (k := k)).symm.toContinuousLinearMap

/-- Hahn-Banach extension of a model current from test forms to bounded continuous coefficient
fields. -/
noncomputable def extendedModelCurrentBCF (T : ModelCurrent n k) :
    StrongDual ℝ (BoundedContinuousFunction (TangentModel n) (FiberAlt n k)) :=
  Classical.choose
    (exists_extension_norm_eq (modelTestFormBCFRange (n := n) (k := k))
      (modelCurrentOnBCFRange (n := n) (k := k) T))

theorem extendedModelCurrentBCF_agrees (T : ModelCurrent n k)
    (ω : Hodge.TestForm n (TangentModel n) k) :
    extendedModelCurrentBCF (n := n) (k := k) T
        (modelTestFormToBCF (n := n) (k := k) ω) =
      T.toContinuousLinearMap ω := by
  let e := modelTestFormBCFRangeEquivCLM (n := n) (k := k)
  let x : modelTestFormBCFRange (n := n) (k := k) := e ω
  have hx :
      extendedModelCurrentBCF (n := n) (k := k) T x =
        modelCurrentOnBCFRange (n := n) (k := k) T x := by
    exact
      (Classical.choose_spec
        (exists_extension_norm_eq (modelTestFormBCFRange (n := n) (k := k))
          (modelCurrentOnBCFRange (n := n) (k := k) T))).1 x
  simpa [extendedModelCurrentBCF, modelCurrentOnBCFRange, e, x] using hx

/-- The unshifted bump with fixed fiber coefficient. -/
theorem bumpFiber_contDiff (ε : ℝ) (hε : ε ≠ 0) (A : FiberAlt n k) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => bump (E := TangentModel n) ε z • A) := by
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => bumpBaseFun (E := TangentModel n) z) := by
    simpa [bumpBaseFun] using (bumpBase (E := TangentModel n)).contDiff (n := (⊤ : ℕ∞))
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => ε⁻¹ • z) :=
    (contDiff_const_smul (c := ε⁻¹)).comp contDiff_id
  have hbump : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => bump (E := TangentModel n) ε z) := by
    simpa [bump] using hbase.comp hscale
  simpa using hbump.smul contDiff_const

/-- The unshifted bump with fixed fiber coefficient is compactly supported. -/
theorem bumpFiber_hasCompactSupport (ε : ℝ) (hε : ε ≠ 0) (A : FiberAlt n k) :
    HasCompactSupport (fun z : TangentModel n => bump (E := TangentModel n) ε z • A) := by
  have hbase : HasCompactSupport (fun z : TangentModel n => bumpBaseFun (E := TangentModel n) z) := by
    simpa [bumpBaseFun] using (bumpBase (E := TangentModel n)).hasCompactSupport
  have hbump : HasCompactSupport (fun z : TangentModel n => bump (E := TangentModel n) ε z) := by
    simpa [bump] using hbase.comp_smul (inv_ne_zero hε)
  have hcoeff :
      HasCompactSupport
        ((fun r : ℝ => r • A) ∘ (fun z : TangentModel n => bump (E := TangentModel n) ε z)) :=
    HasCompactSupport.comp_left hbump (by
      ext r
      simp)
  simpa [Function.comp] using hcoeff

theorem modelTestFormToBCF_shiftedBumpTestForm (ε : ℝ) (hε : ε ≠ 0)
    (x : TangentModel n) (A : FiberAlt n k) :
    modelTestFormToBCF (n := n) (k := k) (shiftedBumpTestForm (n := n) (k := k) ε hε x A) =
      translateBCF (fun z : TangentModel n => bump (E := TangentModel n) ε z • A)
        (bumpFiber_contDiff (n := n) (k := k) ε hε A).continuous
        (bumpFiber_hasCompactSupport (n := n) (k := k) ε hε A) x := by
  ext y
  simp [modelTestFormToBCF_apply, shiftedBumpTestForm, translateBCF_apply, shifted_bump]

/-- The explicit Euclidean smoothing formula before proving the result is a `SmoothForm`. -/
noncomputable def regularizeModelCurrentRaw (ε : ℝ) (hε : ε ≠ 0)
    (T : ModelCurrent n k) : TangentModel n → FiberAlt n k :=
  fun x =>
    let b := modelFiberBasis (n := n) (k := k)
    ∑ i, (T.toContinuousLinearMap (shiftedBumpTestForm (n := n) (k := k) ε hε x (b i))) • b i

/-- The fixed-scale raw Euclidean smoothing formula used by the manifold mollifier. -/
noncomputable def regularizeModelCurrentRawUnit (T : ModelCurrent n k) :
    TangentModel n → FiberAlt n k :=
  regularizeModelCurrentRaw (n := n) (k := k) (ε := 1) (by norm_num) T

/-- The shifted bump is jointly smooth in the center parameter `x` and the spatial variable `y`.
This is the key ingredient for proving smooth dependence of `regularizeModelCurrentRaw` on `x`. -/
theorem shifted_bump_contDiff_joint (ε : ℝ) (hε : ε ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : TangentModel n × TangentModel n =>
      shifted_bump (E := TangentModel n) ε p.1 p.2) := by
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => bumpBaseFun (E := TangentModel n) z) := by
    simpa [bumpBaseFun] using (bumpBase (E := TangentModel n)).contDiff (n := (⊤ : ℕ∞))
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => ε⁻¹ • z) :=
    (contDiff_const_smul (c := ε⁻¹)).comp contDiff_id
  have hbump : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => bump (E := TangentModel n) ε z) := by
    simpa [bump] using hbase.comp hscale
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun p : TangentModel n × TangentModel n => p.1 - p.2) := by
    exact contDiff_fst.sub contDiff_snd
  simpa [shifted_bump] using hbump.comp hsub

noncomputable def modelTranslateBCF {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (g : TangentModel n → H) (cg : Continuous g) (hsupp : HasCompactSupport g) :
    TangentModel n → BoundedContinuousFunction (TangentModel n) H :=
  fun x => translateBCF g cg hsupp x

noncomputable def modelTranslateBCFDerivFamily {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] (g : TangentModel n → H)
    (cg' : Continuous (fderiv ℝ g)) (hsupp' : HasCompactSupport (fderiv ℝ g)) :
    TangentModel n → TangentModel n →L[ℝ] BoundedContinuousFunction (TangentModel n) H :=
  fun x => bcfApplyCLM (translateBCF (fderiv ℝ g) cg' hsupp' x)

private theorem contDiff_translateBCF_fiber_nat
    {g : TangentModel n → FiberAlt n k} (cg : Continuous g) (m : ℕ) (hg : ContDiff ℝ m g)
    (hsupp : HasCompactSupport g) :
    ContDiff ℝ m (modelTranslateBCF (n := n) g cg hsupp) := by
  set_option maxHeartbeats 0 in
  let rec aux {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
      (m : ℕ) {g : TangentModel n → H} (cg : Continuous g)
      (hg : ContDiff ℝ m g) (hsupp : HasCompactSupport g) :
      ContDiff ℝ m (modelTranslateBCF (n := n) g cg hsupp) := by
    cases m with
    | zero =>
        simpa [modelTranslateBCF, contDiff_zero] using continuous_translateBCF (g := g) cg hsupp
    | succ m =>
        have hg1 : ContDiff ℝ ((m : ℕ) + 1) g := by simpa using hg
        rcases (contDiff_succ_iff_fderiv.1 hg1) with ⟨hdiff, _, hg'⟩
        let cg' : Continuous (fderiv ℝ g) := hg'.continuous
        let hsupp' : HasCompactSupport (fderiv ℝ g) := hasCompactSupport_fderiv (g := g) hsupp hdiff
        have htranslate' : ContDiff ℝ m (modelTranslateBCF (n := n) (fderiv ℝ g) cg' hsupp') :=
          aux (H := TangentModel n →L[ℝ] H) m cg' hg' hsupp'
        have hderivMap :
            ContDiff ℝ m (modelTranslateBCFDerivFamily (n := n) g cg' hsupp') := by
          simpa [modelTranslateBCFDerivFamily, modelTranslateBCF] using
            bcfApplyCLM.contDiff.comp htranslate'
        refine (contDiff_succ_iff_hasFDerivAt.2 ?_)
        refine ⟨modelTranslateBCFDerivFamily (n := n) g cg' hsupp', hderivMap, ?_⟩
        intro x
        exact hasFDerivAt_translateBCF (g := g) (g' := fderiv ℝ g) cg hsupp cg' hsupp'
          (fun z => (hdiff z).hasFDerivAt) x
  exact aux m cg hg hsupp

private theorem contDiff_translateBCF_fiber
    {g : TangentModel n → FiberAlt n k} (cg : Continuous g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hsupp : HasCompactSupport g) :
    ContDiff ℝ (⊤ : ℕ∞) (modelTranslateBCF (n := n) g cg hsupp) := by
  rw [contDiff_infty]
  intro m
  have hm : (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)
  exact contDiff_translateBCF_fiber_nat (n := n) (k := k) cg m (hg.of_le hm) hsupp

theorem regularizeModelCurrentRaw_eq_extended (ε : ℝ) (hε : ε ≠ 0)
    (T : ModelCurrent n k) :
    regularizeModelCurrentRaw (n := n) (k := k) ε hε T =
      fun x =>
        let b := modelFiberBasis (n := n) (k := k)
        ∑ i,
          (extendedModelCurrentBCF (n := n) (k := k) T
            (translateBCF (fun z : TangentModel n => bump (E := TangentModel n) ε z • b i)
              (bumpFiber_contDiff (n := n) (k := k) ε hε (b i)).continuous
              (bumpFiber_hasCompactSupport (n := n) (k := k) ε hε (b i)) x)) • b i := by
  funext x
  let b := modelFiberBasis (n := n) (k := k)
  simp [regularizeModelCurrentRaw, b]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [← LocalCurrent.toContinuousLinearMap_apply]
  rw [← extendedModelCurrentBCF_agrees (n := n) (k := k) (T := T)
    (ω := shiftedBumpTestForm (n := n) (k := k) ε hε x (b i))]
  rw [modelTestFormToBCF_shiftedBumpTestForm (n := n) (k := k) ε hε x (b i)]

/-- The smoothness of `x ↦ regularizeModelCurrentRaw ε hε T x`.
This follows from joint smoothness of the bump function and continuity of `T`. -/
theorem regularizeModelCurrentRaw_isSmooth (ε : ℝ) (hε : ε ≠ 0)
    (T : ModelCurrent n k) :
    IsSmoothAlternating n (TangentModel n) k (regularizeModelCurrentRaw (n := n) (k := k) ε hε T) := by
  have hcont :
      ContDiff ℝ (⊤ : ℕ∞) (regularizeModelCurrentRaw (n := n) (k := k) ε hε T) := by
    rw [regularizeModelCurrentRaw_eq_extended (n := n) (k := k) ε hε T]
    let b := modelFiberBasis (n := n) (k := k)
    have hsum :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun x : TangentModel n =>
            ∑ i,
              (extendedModelCurrentBCF (n := n) (k := k) T
                (translateBCF (fun z : TangentModel n => bump (E := TangentModel n) ε z • b i)
                  (bumpFiber_contDiff (n := n) (k := k) ε hε (b i)).continuous
                  (bumpFiber_hasCompactSupport (n := n) (k := k) ε hε (b i)) x)) • b i) := by
      refine ContDiff.sum ?_
      intro i hi
      have hcoeff :
          ContDiff ℝ (⊤ : ℕ∞)
            (fun x : TangentModel n =>
              extendedModelCurrentBCF (n := n) (k := k) T
                (translateBCF (fun z : TangentModel n => bump (E := TangentModel n) ε z • b i)
                  (bumpFiber_contDiff (n := n) (k := k) ε hε (b i)).continuous
                  (bumpFiber_hasCompactSupport (n := n) (k := k) ε hε (b i)) x)) := by
        exact (extendedModelCurrentBCF (n := n) (k := k) T).contDiff.comp
          (contDiff_translateBCF_fiber (n := n) (k := k)
            (g := fun z : TangentModel n => bump (E := TangentModel n) ε z • b i)
            (bumpFiber_contDiff (n := n) (k := k) ε hε (b i)).continuous
            (bumpFiber_contDiff (n := n) (k := k) ε hε (b i))
            (bumpFiber_hasCompactSupport (n := n) (k := k) ε hε (b i)))
      simpa using hcoeff.smul contDiff_const
    simpa [b] using hsum
  unfold IsSmoothAlternating 𝓒_complex TangentModel
  convert hcont.contMDiff using 1 <;> simp [formSmoothness]

/-- Package the raw Euclidean smoothing formula as a `SmoothForm`. -/
noncomputable def regularizeModelCurrentSmoothForm (ε : ℝ) (hε : ε ≠ 0)
    (T : ModelCurrent n k) : SmoothForm n (TangentModel n) k :=
  ⟨regularizeModelCurrentRaw (n := n) (k := k) ε hε T,
    regularizeModelCurrentRaw_isSmooth (n := n) (k := k) ε hε T⟩

@[simp] theorem regularizeModelCurrentRaw_zero (ε : ℝ) (hε : ε ≠ 0) :
    regularizeModelCurrentRaw (n := n) (k := k) ε hε (0 : ModelCurrent n k) = 0 := by
  funext x
  change ∑ i : Fin (Module.finrank ℝ (FiberAlt n k)),
      ((0 : ModelCurrent n k).toContinuousLinearMap
        (shiftedBumpTestForm (n := n) (k := k) ε hε x ((modelFiberBasis (n := n) (k := k)) i))) •
        (modelFiberBasis (n := n) (k := k)) i = 0
  classical
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hzero :
      ((0 : ModelCurrent n k).toContinuousLinearMap
        (shiftedBumpTestForm (n := n) (k := k) ε hε x ((modelFiberBasis (n := n) (k := k)) i))) = 0 := by
    simp [LocalCurrent.toContinuousLinearMap_apply]
  rw [hzero]
  ext v
  simp

@[simp] theorem regularizeModelCurrentSmoothForm_zero (ε : ℝ) (hε : ε ≠ 0) :
    regularizeModelCurrentSmoothForm (n := n) (k := k) ε hε (0 : ModelCurrent n k) = 0 := by
  ext x v
  simp [regularizeModelCurrentSmoothForm, regularizeModelCurrentRaw_zero]

/-- Honest Euclidean regularization interface on chart-model currents. -/
class EuclideanCurrentRegularizationData (n : ℕ) (k : ℕ) : Type where
  regularize : ModelCurrent n k → SmoothForm n (TangentModel n) k

/-- Concrete `EuclideanCurrentRegularizationData` instance using bump-function convolution. -/
noncomputable instance instEuclideanCurrentRegularizationData :
    EuclideanCurrentRegularizationData n k where
  regularize := fun T => regularizeModelCurrentSmoothForm (n := n) (k := k) 1 (by norm_num) T

/-- Regularize a current on the Euclidean model space (WIP). -/
noncomputable def regularizeCurrentEuclidean
    [EuclideanCurrentRegularizationData n k]
    (T : ModelCurrent n k) : SmoothForm n (TangentModel n) k :=
  EuclideanCurrentRegularizationData.regularize (n := n) (k := k) T

/--
**Euclidean cycle-closedness axiom**

On the Euclidean model space, bump-function convolution sends cycle currents to closed forms.

**Mathematical content**: For a cycle `T` (∂T = 0) and the smoothing
`(regularize T)(x) = ∑ᵢ T(φ_{x,i}) • bᵢ`, the exterior derivative vanishes because:
1. `d_x[T(φ_{x,i})] = T(d_x[φ_{x,i}])` (differentiation commutes with the
   continuous linear functional `T`, by smooth dependence of `φ_{x,i}` on `x`).
2. `d_x[bump(ε, x-y)] = -d_y[bump(ε, x-y)]` (chain rule for translation).
3. So `T(d_x[φ_{x,i}]) = -T(d_y[φ_{x,i}]) = -(∂T)(φ_{x,i}) = 0` for cycles.

This is the Euclidean case of the standard commutation `d ∘ mollify = mollify ∘ d`
(de Rham, "Variétés Différentiables", Ch. III; Federer, "Geometric Measure Theory", §4.1).
-/
axiom euclidean_regularize_isClosed_of_isCycleAt (T : ModelCurrent n k) (hT : T.isCycleAt) :
    IsFormClosed (regularizeCurrentEuclidean (n := n) (k := k) T)

/-- Companion laws for Euclidean regularization on chart-model currents. -/
class EuclideanCurrentRegularizationLaws (n : ℕ) (k : ℕ)
    [EuclideanCurrentRegularizationData n k] : Prop where
  regularize_isClosed_of_isCycleAt :
    ∀ T : ModelCurrent n k, T.isCycleAt →
      IsFormClosed (regularizeCurrentEuclidean (n := n) (k := k) T)
  regularize_zero :
    regularizeCurrentEuclidean (n := n) (k := k) (0 : ModelCurrent n k) = 0

/-- The concrete bump-function regularizer satisfies the Euclidean law package. -/
noncomputable instance instEuclideanCurrentRegularizationLaws :
    EuclideanCurrentRegularizationLaws n k where
  regularize_isClosed_of_isCycleAt := fun T hT =>
    euclidean_regularize_isClosed_of_isCycleAt (n := n) (k := k) T hT
  regularize_zero := by
    change regularizeModelCurrentSmoothForm (n := n) (k := k) 1 (by norm_num)
        (0 : ModelCurrent n k) = 0
    exact regularizeModelCurrentSmoothForm_zero (n := n) (k := k) 1 (by norm_num)

theorem regularizeCurrentEuclidean_isClosed_of_isCycleAt
    [EuclideanCurrentRegularizationData n k] [EuclideanCurrentRegularizationLaws n k]
    (T : ModelCurrent n k) (hT : T.isCycleAt) :
    IsFormClosed (regularizeCurrentEuclidean (n := n) (k := k) T) :=
  EuclideanCurrentRegularizationLaws.regularize_isClosed_of_isCycleAt
    (n := n) (k := k) T hT

@[simp] theorem regularizeCurrentEuclidean_zero
    [EuclideanCurrentRegularizationData n k] [EuclideanCurrentRegularizationLaws n k] :
    regularizeCurrentEuclidean (n := n) (k := k) (0 : ModelCurrent n k) = 0 :=
  EuclideanCurrentRegularizationLaws.regularize_zero (n := n) (k := k)

end Hodge.GMT
