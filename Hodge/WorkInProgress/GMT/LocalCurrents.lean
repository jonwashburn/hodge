import Hodge.Analytic.Currents
import Hodge.Analytic.TestForms
import Hodge.WorkInProgress.Analytic.Pullback

noncomputable section

open Classical
open scoped Manifold
open scoped Pointwise

namespace Hodge

universe u v

variable {n : ℕ}

/-- The Euclidean model space has constant identity charts. -/
instance instHasLocallyConstantCharts_TangentModel :
    HasLocallyConstantCharts n (TangentModel n) := by
  refine ⟨?_⟩
  intro x y hy
  simp

namespace TestForm

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  {k : ℕ}

/-- Comass on compactly supported forms, defined without a global compactness assumption on `X`. -/
noncomputable def comass (ω : TestForm n X k) : ℝ :=
  sSup (Set.range (pointwiseComass (α := (ω : SmoothForm n X k))))

theorem comass_nonneg (ω : TestForm n X k) : 0 ≤ comass ω := by
  unfold comass
  apply Real.sSup_nonneg
  intro r hr
  rcases hr with ⟨x, rfl⟩
  exact pointwiseComass_nonneg (α := (ω : SmoothForm n X k)) x

private theorem pointwiseComass_eq_zero_of_not_mem_tsupport
    (ω : TestForm n X k) {x : X}
    (hx : x ∉ tsupport ((ω : SmoothForm n X k).as_alternating)) :
    pointwiseComass (α := (ω : SmoothForm n X k)) x = 0 := by
  have hxzero : (ω : SmoothForm n X k).as_alternating x = 0 := by
    by_contra hne
    exact hx (subset_tsupport _ (by simpa [Function.mem_support] using hne))
  simp [pointwiseComass, hxzero]

theorem comass_bddAbove (ω : TestForm n X k) :
    BddAbove (Set.range (pointwiseComass (α := (ω : SmoothForm n X k)))) := by
  let f : X → ℝ := fun x => pointwiseComass (α := (ω : SmoothForm n X k)) x
  have hcont : Continuous f := by
    simpa [f, pointwiseComass] using
      (continuous_norm.comp ((ω : SmoothForm n X k).is_smooth.continuous))
  have hcompact : IsCompact (tsupport ((ω : SmoothForm n X k).as_alternating)) := by
    simpa [HasCompactSupport] using ω.2
  rcases (hcompact.image hcont).bddAbove with ⟨M, hM⟩
  refine ⟨max M 0, ?_⟩
  rintro r ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport ((ω : SmoothForm n X k).as_alternating)
  · have hxM : f x ≤ M := hM ⟨x, hx, rfl⟩
    exact hxM.trans (le_max_left _ _)
  · have hzero : f x = 0 := by
      simpa [f] using pointwiseComass_eq_zero_of_not_mem_tsupport (ω := ω) hx
    simpa [f, hzero] using (le_max_right M 0)

theorem pointwiseComass_le_comass (ω : TestForm n X k) (x : X) :
    pointwiseComass (α := (ω : SmoothForm n X k)) x ≤ comass ω := by
  unfold comass
  exact le_csSup (comass_bddAbove ω) ⟨x, rfl⟩

@[simp] theorem comass_zero [Nonempty X] : comass (0 : TestForm n X k) = 0 := by
  unfold comass
  have h : Set.range (pointwiseComass (α := ((0 : TestForm n X k) : SmoothForm n X k))) = {0} := by
    ext r
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro hr
      rcases hr with ⟨x, rfl⟩
      simp [pointwiseComass]
    · intro hr
      refine ⟨Classical.choice inferInstance, ?_⟩
      simp [pointwiseComass, hr]
  rw [h]
  exact csSup_singleton 0

theorem comass_add_le [Nonempty X] (ω η : TestForm n X k) :
    comass (ω + η) ≤ comass ω + comass η := by
  unfold comass
  apply csSup_le
  · exact Set.range_nonempty _
  · intro r hr
    rcases hr with ⟨x, rfl⟩
    calc
      pointwiseComass (α := ((ω + η : TestForm n X k) : SmoothForm n X k)) x
          ≤ pointwiseComass (α := (ω : SmoothForm n X k)) x +
              pointwiseComass (α := (η : SmoothForm n X k)) x :=
            pointwiseComass_add_le (α := (ω : SmoothForm n X k))
              (β := (η : SmoothForm n X k)) x
      _ ≤ sSup (Set.range (pointwiseComass (α := (ω : SmoothForm n X k)))) +
            sSup (Set.range (pointwiseComass (α := (η : SmoothForm n X k)))) := by
          apply add_le_add
          · exact le_csSup (comass_bddAbove ω) ⟨x, rfl⟩
          · exact le_csSup (comass_bddAbove η) ⟨x, rfl⟩

theorem hasCompactSupport_of_compactSpace [CompactSpace X] (ω : SmoothForm n X k) :
    HasCompactSupport ω.as_alternating := by
  simpa [HasCompactSupport] using
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

/-- Real scalar multiplication preserves compact support. -/
instance : SMul ℝ (TestForm n X k) :=
  ⟨fun r ω =>
    ⟨r • (ω : SmoothForm n X k), by
      have h :
          HasCompactSupport ((fun y : FiberAlt n k => r • y) ∘ (ω : SmoothForm n X k).as_alternating) :=
        HasCompactSupport.comp_left ω.2 (by
          ext v
          simp)
      simpa [Function.comp] using h⟩⟩

@[simp] theorem coe_smul_real (r : ℝ) (ω : TestForm n X k) :
    ((r • ω : TestForm n X k) : SmoothForm n X k) = r • (ω : SmoothForm n X k) := rfl

theorem comass_smul [Nonempty X] (r : ℝ) (ω : TestForm n X k) :
    comass (r • ω) = |r| * comass ω := by
  unfold comass
  have h_range :
      Set.range (pointwiseComass (α := ((r • ω : TestForm n X k) : SmoothForm n X k))) =
        (|r|) • Set.range (pointwiseComass (α := (ω : SmoothForm n X k))) := by
    ext t
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨pointwiseComass (α := (ω : SmoothForm n X k)) x, ⟨x, rfl⟩, ?_⟩
      simp [pointwiseComass_smul]
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      refine ⟨x, ?_⟩
      simp [pointwiseComass_smul]
  rw [h_range]
  rw [Real.sSup_smul_of_nonneg (abs_nonneg r) (Set.range (pointwiseComass (α := (ω : SmoothForm n X k)))),
    smul_eq_mul]

instance : AddCommGroup (TestForm n X k) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  sub := (· - ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro ω η θ
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    simp [add_assoc]
  zero_add := by
    intro ω
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    simp
  add_zero := by
    intro ω
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    simp
  neg_add_cancel := by
    intro ω
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    simp
  add_comm := by
    intro ω η
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    simp [add_comm]
  sub_eq_add_neg := by
    intro ω η
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    simp [sub_eq_add_neg]

instance : Module ℝ (TestForm n X k) where
  one_smul ω := by
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    simp
  mul_smul r s ω := by
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    ext v
    simp [mul_assoc]
  smul_zero r := by
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    simp
  smul_add r ω η := by
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    ext v
    simpa using
      (_root_.mul_add (r : ℂ) (((ω : SmoothForm n X k).as_alternating x) v)
        (((η : SmoothForm n X k).as_alternating x) v))
  add_smul r s ω := by
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    ext v
    simpa using
      (_root_.add_mul (r : ℂ) (s : ℂ) (((ω : SmoothForm n X k).as_alternating x) v))
  zero_smul ω := by
    apply Subtype.ext
    apply SmoothForm.ext
    funext x
    simp

instance : Norm (TestForm n X k) := ⟨comass⟩

instance [Nonempty X] : SeminormedAddCommGroup (TestForm n X k) := by
  classical
  refine SeminormedAddCommGroup.ofCore (𝕜 := ℝ) (E := TestForm n X k)
    { norm_nonneg := fun ω => comass_nonneg ω
      norm_smul := fun r ω => by
        simpa [Real.norm_eq_abs] using comass_smul (r := r) ω
      norm_triangle := fun ω η => by
        simpa using comass_add_le ω η }

instance [Nonempty X] : NormedSpace ℝ (TestForm n X k) where
  norm_smul_le r ω := by
    change comass (r • ω) ≤ |r| * comass ω
    simpa using (le_of_eq (comass_smul (r := r) ω))

/-- Exterior derivative preserves compact support on test forms. -/
noncomputable def smoothExtDeriv (ω : TestForm n X k) : TestForm n X (k + 1) :=
  ⟨_root_.smoothExtDeriv (ω : SmoothForm n X k),
    smoothExtDeriv_hasCompactSupport (ω := (ω : SmoothForm n X k)) ω.2⟩

@[simp] theorem coe_smoothExtDeriv (ω : TestForm n X k) :
    ((smoothExtDeriv ω : TestForm n X (k + 1)) : SmoothForm n X (k + 1)) =
      _root_.smoothExtDeriv (ω : SmoothForm n X k) := rfl

@[simp] theorem smoothExtDeriv_zero :
    smoothExtDeriv (0 : TestForm n X k) = 0 := by
  apply Subtype.ext
  simp [smoothExtDeriv]

@[simp] theorem smoothExtDeriv_add (ω η : TestForm n X k) :
    smoothExtDeriv (ω + η) = smoothExtDeriv ω + smoothExtDeriv η := by
  apply Subtype.ext
  simp [smoothExtDeriv, _root_.smoothExtDeriv_add]

@[simp] theorem smoothExtDeriv_smul_real (r : ℝ) (ω : TestForm n X k) :
    smoothExtDeriv (r • ω) = r • smoothExtDeriv ω := by
  apply Subtype.ext
  simp [smoothExtDeriv, _root_.smoothExtDeriv_smul_real]

@[simp] theorem smoothExtDeriv_extDeriv (ω : TestForm n X k) :
    smoothExtDeriv (smoothExtDeriv ω) = 0 := by
  apply Subtype.ext
  simp [smoothExtDeriv, _root_.smoothExtDeriv_extDeriv]

variable {Y : Type v} [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) Y]
  [IsManifold (𝓒_complex n) ⊤ Y] [HasLocallyConstantCharts n Y]

/-- Pull back a compactly supported test form to a compact source manifold. -/
noncomputable def pullbackToSmooth [CompactSpace X]
    (f : X → Y) (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f)
    (ω : TestForm n Y k) : SmoothForm n X k :=
  smoothFormPullback (n := n) f hf (ω : SmoothForm n Y k)

@[simp] theorem pullbackToSmooth_add [CompactSpace X]
    (f : X → Y) (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f)
    (ω₁ ω₂ : TestForm n Y k) :
    pullbackToSmooth (n := n) f hf (ω₁ + ω₂) =
      pullbackToSmooth (n := n) f hf ω₁ + pullbackToSmooth (n := n) f hf ω₂ := by
  simpa [pullbackToSmooth] using
    (SmoothForm.pullback_add (n := n) (f := f) hf
      (ω₁ := (ω₁ : SmoothForm n Y k)) (ω₂ := (ω₂ : SmoothForm n Y k)))

@[simp] theorem pullbackToSmooth_smul [CompactSpace X]
    (f : X → Y) (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f)
    (r : ℝ) (ω : TestForm n Y k) :
    pullbackToSmooth (n := n) f hf (r • ω) =
      r • pullbackToSmooth (n := n) f hf ω := by
  simpa [pullbackToSmooth] using
    (SmoothForm.pullback_smul (n := n) (f := f) hf r
      (ω := (ω : SmoothForm n Y k)))

@[simp] theorem pullbackToSmooth_smoothExtDeriv [CompactSpace X]
    (f : X → Y) (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f)
    (ω : TestForm n Y k) :
    pullbackToSmooth (n := n) f hf (smoothExtDeriv ω) =
      _root_.smoothExtDeriv (pullbackToSmooth (n := n) f hf ω) := by
  simpa [pullbackToSmooth, smoothExtDeriv] using
    (smoothExtDeriv_pullback (n := n) (f := f)
      (ω := (ω : SmoothForm n Y k)) hf)

theorem pullbackToSmooth_congr [CompactSpace X]
    (f g : X → Y) (hfg : f = g)
    (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f)
    (hg : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ g)
    (ω : TestForm n Y k) :
    pullbackToSmooth (n := n) f hf ω = pullbackToSmooth (n := n) g hg ω := by
  subst hfg
  simpa [pullbackToSmooth] using
    (SmoothForm.pullback_congr (n := n) (f := f) (g := f) rfl hf hg (ω : SmoothForm n Y k))

/-- Pullback from a compact source has comass bounded by the source derivative bound. -/
theorem pullbackToSmooth_norm_le [CompactSpace X] [Nonempty X]
    (f : X → Y) (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f)
    (C : ℝ) (hC : ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C)
    (ω : TestForm n Y k) :
    ‖pullbackToSmooth (n := n) f hf ω‖ ≤ comass ω * C := by
  classical
  have h_pointwise :
      ∀ x,
        pointwiseComass (α := pullbackToSmooth (n := n) f hf ω) x ≤ comass ω * C := by
    intro x
    have h_pull :
        ‖fiberPullback (n := n)
            (mfderiv (𝓒_complex n) (𝓒_complex n) f x)
            ((ω : SmoothForm n Y k).as_alternating (f x))‖ ≤
          ‖(ω : SmoothForm n Y k).as_alternating (f x)‖ *
            ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k := by
      simpa using
        (fiberPullback_norm_le (n := n)
          (L := mfderiv (𝓒_complex n) (𝓒_complex n) f x)
          (ω := (ω : SmoothForm n Y k).as_alternating (f x)))
    have hω :
        ‖(ω : SmoothForm n Y k).as_alternating (f x)‖ ≤ comass ω := by
      simpa [pointwiseComass] using pointwiseComass_le_comass (ω := ω) (x := f x)
    have h_mul :
        ‖(ω : SmoothForm n Y k).as_alternating (f x)‖ *
            ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤
          comass ω * C := by
      have hmf_nonneg : 0 ≤ ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k := by
        exact pow_nonneg (norm_nonneg _) _
      exact mul_le_mul hω (hC x) hmf_nonneg (comass_nonneg ω)
    have h_pointwise' :
        pointwiseComass (α := pullbackToSmooth (n := n) f hf ω) x ≤
          ‖(ω : SmoothForm n Y k).as_alternating (f x)‖ *
            ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k := by
      simpa [pointwiseComass, pullbackToSmooth] using h_pull
    exact h_pointwise'.trans h_mul
  change _root_.comass (pullbackToSmooth (n := n) f hf ω) ≤ comass ω * C
  unfold _root_.comass
  apply csSup_le
  · exact Set.range_nonempty _
  · intro r hr
    rcases hr with ⟨x, rfl⟩
    exact h_pointwise x

end TestForm

end Hodge

namespace Hodge.GMT

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]

/-- A local current acts on compactly supported smooth forms, so it does not require
global compact/projective/Kähler structure on its ambient space. -/
structure LocalCurrent (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] where
  toLinear : Hodge.TestForm n X k →ₗ[ℝ] ℝ
  comass_bound :
    ∃ M : ℝ, ∀ ω : Hodge.TestForm n X k, |toLinear ω| ≤ M * Hodge.TestForm.comass ω
  boundary_bound :
    match k with
    | 0 => True
    | k' + 1 =>
        ∃ M : ℝ, ∀ ω : Hodge.TestForm n X k',
          |toLinear (Hodge.TestForm.smoothExtDeriv ω)| ≤ M * Hodge.TestForm.comass ω

namespace LocalCurrent

variable [Nonempty X]

/-- Local currents are continuous linear functionals for the test-form comass seminorm. -/
noncomputable def toContinuousLinearMap (T : LocalCurrent n X k) :
    Hodge.TestForm n X k →L[ℝ] ℝ := by
  classical
  let f : Hodge.TestForm n X k →ₗ[ℝ] ℝ := T.toLinear
  let M : ℝ := Classical.choose T.comass_bound
  let hM : ∀ ω : Hodge.TestForm n X k, |T.toLinear ω| ≤ M * Hodge.TestForm.comass ω :=
    Classical.choose_spec T.comass_bound
  have hbound : ∃ C : ℝ, ∀ ω : Hodge.TestForm n X k, ‖f ω‖ ≤ C * ‖ω‖ := by
    refine ⟨M, ?_⟩
    intro ω
    simpa [f, Real.norm_eq_abs, Hodge.TestForm.comass] using hM ω
  exact f.mkContinuousOfExistsBound hbound

@[simp] theorem toContinuousLinearMap_apply (T : LocalCurrent n X k) (ω : Hodge.TestForm n X k) :
    T.toContinuousLinearMap ω = T.toLinear ω := by
  simp [toContinuousLinearMap, LinearMap.mkContinuousOfExistsBound_apply]

end LocalCurrent

namespace LocalCurrent

@[ext] theorem ext {S T : LocalCurrent n X k} (h : ∀ ω, S.toLinear ω = T.toLinear ω) :
    S = T := by
  cases S with
  | mk Sto Scom Sbd =>
      cases T with
      | mk Tto Tcom Tbd =>
          have hto : Sto = Tto := by
            ext ω
            exact h ω
          subst hto
          have hcom : Scom = Tcom := by
            apply Subsingleton.elim
          subst hcom
          have hbd : Sbd = Tbd := by
            apply Subsingleton.elim
          subst hbd
          rfl

instance : Zero (LocalCurrent n X k) where
  zero :=
    { toLinear := 0
      comass_bound := by
        refine ⟨0, ?_⟩
        intro ω
        simp [Hodge.TestForm.comass_nonneg]
      boundary_bound := by
        cases k with
        | zero =>
            trivial
        | succ k' =>
            refine ⟨0, ?_⟩
            intro ω
            simp [Hodge.TestForm.comass_nonneg] }

@[simp] theorem zero_toLinear (ω : Hodge.TestForm n X k) :
    (0 : LocalCurrent n X k).toLinear ω = 0 := rfl

/-- Boundary of a local current, defined using compactly supported test forms. -/
def boundary (T : LocalCurrent n X (k + 1)) : LocalCurrent n X k where
  toLinear :=
    { toFun := fun ω => T.toLinear (Hodge.TestForm.smoothExtDeriv ω)
      map_add' := by
        intro ω₁ ω₂
        simp
      map_smul' := by
        intro r ω
        simp }
  comass_bound := by
    simpa using T.boundary_bound
  boundary_bound := by
    cases k with
    | zero =>
        trivial
    | succ k' =>
        refine ⟨0, ?_⟩
        intro ω
        simp [Hodge.TestForm.comass_nonneg]

@[simp] theorem boundary_toLinear (T : LocalCurrent n X (k + 1)) (ω : Hodge.TestForm n X k) :
    (boundary T).toLinear ω = T.toLinear (Hodge.TestForm.smoothExtDeriv ω) := rfl

/-- Positive-degree local currents with vanishing boundary. -/
def isCycle (T : LocalCurrent n X (k + 1)) : Prop := boundary T = 0

/-- Degree-uniform cycle predicate for local currents. -/
def isCycleAt : {k : ℕ} → LocalCurrent n X k → Prop
  | 0, _ => True
  | _ + 1, T => isCycle T

@[simp] theorem isCycleAt_zero (T : LocalCurrent n X 0) : T.isCycleAt := trivial

@[simp] theorem isCycleAt_succ_iff (T : LocalCurrent n X (k + 1)) :
    T.isCycleAt ↔ LocalCurrent.boundary T = 0 := Iff.rfl

@[simp] theorem boundary_zero : boundary (0 : LocalCurrent n X (k + 1)) = 0 := by
  ext ω
  simp [boundary]

theorem boundary_boundary (T : LocalCurrent n X (k + 2)) :
    boundary (boundary T) = 0 := by
  ext ω
  simp [boundary]

end LocalCurrent

/-- Local currents on the Euclidean chart model. -/
abbrev ModelCurrent (n : ℕ) (k : ℕ) :=
  LocalCurrent n (TangentModel n) k

end Hodge.GMT
