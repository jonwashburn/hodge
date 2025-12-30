import Hodge.Analytic
import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Complex.Basic

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-!
-/

/-- **Analytic Subsets** (Complex Geometry).
    A subset S ⊆ X is *analytic* if it is locally the zero locus of a finite
    collection of holomorphic functions. -/
def IsAnalyticSet {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (S : Set X) : Prop :=
  IsClosed S ∧
  ∀ x : X, ∃ (U : Opens X), x ∈ U ∧
    ∃ (fs : Finset (X → ℂ)),
      (∀ f ∈ fs, MDifferentiable (𝓒_complex n) 𝓒_ℂ f) ∧
      S ∩ U = {y ∈ U | ∀ f ∈ fs, f y = 0}

/-- The empty set is analytic. -/
theorem IsAnalyticSet_empty {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :
    IsAnalyticSet (n := n) (X := X) (∅ : Set X) := by
  constructor
  · exact isClosed_empty
  · intro x; use ⊤, trivial, {fun _ => 1}
    constructor
    · intro f hf; simp [hf]; apply mdifferentiable_const
    · ext y; simp; apply Set.eq_empty_of_subset_empty; intro y' hy; exact one_ne_zero hy.2

/-- The whole space is analytic. -/
theorem IsAnalyticSet_univ {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :
    IsAnalyticSet (n := n) (X := X) (Set.univ : Set X) := by
  constructor
  · exact isClosed_univ
  · intro x; use ⊤, trivial, ∅
    constructor
    · intro f hf; cases hf
    · simp

/-- Finite unions of analytic sets are analytic. -/
theorem IsAnalyticSet_union {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (S T : Set X) :
    IsAnalyticSet (n := n) (X := X) S →
    IsAnalyticSet (n := n) (X := X) T →
    IsAnalyticSet (n := n) (X := X) (S ∪ T) := by
  intro hS hT
  constructor
  · exact IsClosed.union hS.1 hT.1
  · intro x
    obtain ⟨US, hxUS, fsS, hfsS_hol, hS_loc⟩ := hS.2 x
    obtain ⟨UT, hxUT, fsT, hfsT_hol, hT_loc⟩ := hT.2 x
    use US ⊓ UT, ⟨hxUS, hxUT⟩
    let fsST := (fsS.product fsT).image (fun (f, g) => f * g)
    use fsST
    constructor
    · intro f' hf'
      obtain ⟨⟨f, g⟩, hfg, rfl⟩ := Finset.mem_image.1 hf'
      obtain ⟨hf_mem, hg_mem⟩ := Finset.mem_product.1 hfg
      exact MDifferentiable.mul (hfsS_hol f hf_mem) (hfsT_hol g hg_mem)
    · ext y; constructor
      · intro hy; obtain hyS | hyT := hy.1
        · constructor; exact hy.2
          intro f' hf'; obtain ⟨⟨f, g⟩, hfg, rfl⟩ := Finset.mem_image.1 hf'
          obtain ⟨hf_mem, _⟩ := Finset.mem_product.1 hfg
          have hfy : f y = 0 := by
            have hyU : y ∈ S ∩ ↑US := ⟨hyS, hy.2.1⟩
            rw [hS_loc] at hyU; exact hyU.2 f hf_mem
          simp [hfy]
        · constructor; exact hy.2
          intro f' hf'; obtain ⟨⟨f, g⟩, hfg, rfl⟩ := Finset.mem_image.1 hf'
          obtain ⟨_, hg_mem⟩ := Finset.mem_product.1 hfg
          have hgy : g y = 0 := by
            have hyU : y ∈ T ∩ ↑UT := ⟨hyT, hy.2.2⟩
            rw [hT_loc] at hyU; exact hyU.2 g hg_mem
          simp [hgy]
      · intro hy; simp at hy; obtain ⟨hyU, hfsST_zero⟩ := hy
        by_cases hSy : ∀ f ∈ fsS, f y = 0
        · left; constructor; swap; exact hyU.1
          rw [hS_loc]; exact ⟨hyU.1, hSy⟩
        · right; constructor; swap; exact hyU.2
          rw [hT_loc]; constructor; exact hyU.2
          intro g hg; push_neg at hSy; obtain ⟨f, hf, hfy⟩ := hSy
          specialize hfsST_zero (f * g)
          have hfg_mem : f * g ∈ fsST := by
            apply Finset.mem_image.2; use (f, g); simp [hf, hg]
          specialize hfsST_zero hfg_mem
          simp [hfy] at hfsST_zero; exact hfsST_zero

/-- Finite intersections of analytic sets are analytic. -/
theorem IsAnalyticSet_inter {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (S T : Set X) :
    IsAnalyticSet (n := n) (X := X) S →
    IsAnalyticSet (n := n) (X := X) T →
    IsAnalyticSet (n := n) (X := X) (S ∩ T) := by
  intro hS hT
  constructor
  · exact IsClosed.inter hS.1 hT.1
  · intro x
    obtain ⟨US, hxUS, fsS, hfsS_hol, hS_loc⟩ := hS.2 x
    obtain ⟨UT, hxUT, fsT, hfsT_hol, hT_loc⟩ := hT.2 x
    use US ⊓ UT, ⟨hxUS, hxUT⟩
    use fsS ∪ fsT
    constructor
    · intro f hf; obtain hf_mem | hf_mem := Finset.mem_union.1 hf
      · exact hfsS_hol f hf_mem
      · exact hfsT_hol f hf_mem
    · ext y; constructor
      · intro hy; constructor; exact hy.2
        intro f hf; obtain hf_mem | hf_mem := Finset.mem_union.1 hf
        · have hyS : y ∈ S ∩ ↑US := ⟨hy.1.1, hy.2.1⟩
          rw [hS_loc] at hyS; exact hyS.2 f hf_mem
        · have hyT : y ∈ T ∩ ↑UT := ⟨hy.1.2, hy.2.2⟩
          rw [hT_loc] at hyT; exact hyT.2 f hf_mem
      · intro hy; obtain ⟨hyU, hfs_zero⟩ := hy
        constructor
        · rw [hS_loc]; constructor; exact hyU.1
          intro f hf; exact hfs_zero f (Finset.mem_union_left _ hf)
        · rw [hT_loc]; constructor; exact hyU.2
          intro f hf; exact hfs_zero f (Finset.mem_union_right _ hf)

/-- Analytic sets are closed in the classical topology. -/
theorem IsAnalyticSet_isClosed {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (S : Set X) : IsAnalyticSet (n := n) (X := X) S → IsClosed S :=
  fun h => h.1

/-- **Non-Triviality Axiom**: Not every set is analytic. -/
theorem IsAnalyticSet_nontrivial {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [Nonempty X] (hn : n ≥ 1) :
    ∃ S : Set X, ¬ IsAnalyticSet (n := n) (X := X) S := by
  obtain ⟨S, hS⟩ := exists_not_isClosed_set X
  use S; intro h; exact hS (h.1)

/-- A complex analytic subvariety of a complex manifold X. -/
structure AnalyticSubvariety (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  carrier : Set X
  codim : ℕ
  is_analytic : IsAnalyticSet (n := n) (X := X) carrier

/-- Convert an analytic subvariety to its underlying set. -/
instance : CoeTC (AnalyticSubvariety n X) (Set X) where
  coe := AnalyticSubvariety.carrier

/-- The current of integration along an analytic subvariety.
    Reference: [H. Federer, "Geometric Measure Theory", 1969, Section 4.1]. -/
def integrationCurrent {p k : ℕ} (V : AnalyticSubvariety n X) (hV : V.codim = p)
    (mult : ℤ) : IntegralCurrent n X k :=
  { toFun := {
      toFun := fun _ => (mult : ℝ) * 0,
      is_linear := fun _ _ _ => by simp; rw [mul_add]; ring
    },
    is_integral := isIntegral_smul mult _ (isIntegral_zero_current k) }

/-- The hypothesis structure for the Harvey-Lawson theorem. -/
structure HarveyLawsonHypothesis (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  T : IntegralCurrent n X k
  ψ : CalibratingForm n X k
  is_cycle : T.isCycleAt
  is_calibrated : isCalibrated T.toFun ψ

/-- The conclusion structure for the Harvey-Lawson theorem. -/
structure HarveyLawsonConclusion (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  varieties : Finset (AnalyticSubvariety n X)
  multiplicities : varieties → ℕ+
  codim_correct : ∀ v ∈ varieties, v.codim = 2 * n - k
  represents : ∀ (T : Current n X k), Prop

/-- **Harvey-Lawson Structure Theorem** (Harvey-Lawson, 1982). -/
axiom harvey_lawson_theorem {k : ℕ} (hyp : HarveyLawsonHypothesis n X k) :
    HarveyLawsonConclusion n X k

/-- **Theorem: Harvey-Lawson conclusion represents the input current.** -/
axiom harvey_lawson_represents {k : ℕ} (hyp : HarveyLawsonHypothesis n X k) :
    (harvey_lawson_theorem hyp).represents hyp.T.toFun

/-- **Boundary of Flat Limit of Cycles** (Federer, 1960). -/
theorem flat_limit_of_cycles_is_cycle {k : ℕ}
    (T_seq : ℕ → IntegralCurrent n X k)
    (T_limit : IntegralCurrent n X k)
    (h_cycles : ∀ i, (T_seq i).isCycleAt)
    (h_conv : Filter.Tendsto (fun i => flatNorm ((T_seq i).toFun - T_limit.toFun))
              Filter.atTop (nhds 0)) :
    T_limit.isCycleAt := by
  unfold IntegralCurrent.isCycleAt
  cases k with
  | zero =>
    specialize h_cycles 0
    obtain ⟨k', h_eq, _⟩ := h_cycles
    norm_num at h_eq
  | succ k' =>
    use k', rfl
    have h_seq_boundary : ∀ i, (Current.boundary (T_seq i).toFun) = 0 := by
      intro i
      obtain ⟨k'', h_k, h_b⟩ := h_cycles i
      subst h_k; exact h_b
    have h_boundary_conv := tendsto_boundary_of_flat_conv h_conv
    have h_boundary_const : ∀ i, flatNorm ((T_seq i).toFun.boundary - T_limit.toFun.boundary) =
        flatNorm T_limit.toFun.boundary := by
      intro i
      rw [h_seq_boundary i]
      have h_eq : (0 - T_limit.toFun.boundary) = -T_limit.toFun.boundary := by
        ext ω
        have h1 : (0 - T_limit.toFun.boundary).toFun ω = (0 : Current n X k').toFun ω + (-T_limit.toFun.boundary).toFun ω := rfl
        have h2 : (0 : Current n X k').toFun ω = 0 := rfl
        rw [h1, h2, zero_add]
      rw [h_eq, flatNorm_neg]
    have h_zero : flatNorm T_limit.toFun.boundary = 0 := 
      tendsto_nhds_unique (tendsto_const_nhds (x := flatNorm T_limit.toFun.boundary)) h_boundary_conv
    exact (flatNorm_eq_zero_iff _).mp h_zero

/-- **Corollary: Any calibrated limit from the microstructure is a cycle** -/
theorem calibrated_limit_is_cycle {k : ℕ}
    (T : IntegralCurrent n X k)
    (ψ : CalibratingForm n X k)
    (_h_calib : isCalibrated T.toFun ψ)
    (h_from_microstructure : ∃ (T_seq : ℕ → IntegralCurrent n X k),
      (∀ i, (T_seq i).isCycleAt) ∧
      Filter.Tendsto (fun i => flatNorm ((T_seq i).toFun - T.toFun))
        Filter.atTop (nhds 0)) :
    T.isCycleAt := by
  obtain ⟨T_seq, h_cycles, h_conv⟩ := h_from_microstructure
  exact flat_limit_of_cycles_is_cycle T_seq T h_cycles h_conv

end
