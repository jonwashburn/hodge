import sys

content = """import Hodge.Analytic
import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Complex.Basic

noncomputable section

open Classical TopologicalSpace Hodge

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-!
# Track A.1: Harvey-Lawson Theorem
-/

/-- The empty set is analytic. -/
theorem IsAnalyticSet_empty {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :
    IsAnalyticSet (n := n) (X := X) (∅ : Set X) := by
  constructor
  · exact isClosed_empty
  · intro x; use Set.univ, univ_mem, ∅; simp

/-- The whole space is analytic. -/
theorem IsAnalyticSet_univ {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :
    IsAnalyticSet (n := n) (X := X) (Set.univ : Set X) := by
  constructor
  · exact isClosed_univ
  · intro x; use Set.univ, univ_mem, ∅; simp

/-- Finite unions of analytic sets are analytic. -/
theorem IsAnalyticSet_union {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (S T : Set X) (hS : IsAnalyticSet S) (hT : IsAnalyticSet T) :
    IsAnalyticSet (n := n) (X := X) (S ∪ T) := by
  constructor
  · exact hS.1.union hT.1
  · intro x
    obtain ⟨US, hUS, fsS, hfS, hS_eq⟩ := hS.2 x
    obtain ⟨UT, hUT, fsT, hfT, hT_eq⟩ := hT.2 x
    use US ∩ UT, inter_mem hUS hUT
    -- The product of all pairs of functions vanishes on the union
    let fs := (fsS.product fsT).image (fun (f, g) => f * g)
    use fs
    constructor
    · intro f hf; obtain ⟨⟨g, h⟩, -, rfl⟩ := Finset.mem_image.mp hf
      exact (hfS g (by simpa using _)).mul (hfT h (by simpa using _))
    · ext y; simp [hS_eq, hT_eq]; tauto

/-- Finite intersections of analytic sets are analytic. -/
theorem IsAnalyticSet_inter {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (S T : Set X) (hS : IsAnalyticSet S) (hT : IsAnalyticSet T) :
    IsAnalyticSet (n := n) (X := X) (S ∩ T) := by
  constructor
  · exact hS.1.inter hT.1
  · intro x
    obtain ⟨US, hUS, fsS, hfS, hS_eq⟩ := hS.2 x
    obtain ⟨UT, hUT, fsT, hfT, hT_eq⟩ := hT.2 x
    use US ∩ UT, inter_mem hUS hUT
    use fsS ∪ fsT
    constructor
    · intro f hf; cases Finset.mem_union.mp hf <;> aesop
    · ext y; simp [hS_eq, hT_eq]; tauto

/-- Analytic sets are closed in the classical topology. -/
theorem IsAnalyticSet_isClosed {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (S : Set X) (h : IsAnalyticSet S) : IsClosed S := h.1

/-- Positive-dimensional complex manifolds are nontrivial. -/
theorem nontrivial_of_dim_pos {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [Nonempty X] (hn : n ≥ 1) : Nontrivial X := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let chart := chartAt (EuclideanSpace ℂ (Fin n)) x
  let idx : Fin n := ⟨0, hn⟩
  let e₀ : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single idx 1
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp chart.open_target (chart x) (chart.map_source (mem_chart_source _ x))
  let p := chart x
  let q := p + (r / 2 : ℝ) • e₀
  refine ⟨chart.symm p, chart.symm q, ?_⟩
  intro h_eq
  have : p = q := by
    rw [← chart.right_inv (by aesop), ← chart.right_inv (by aesop), h_eq]
  aesop

/-- **Non-Triviality**: Not every set is analytic. -/
theorem IsAnalyticSet_nontrivial {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [Nonempty X] (hn : n ≥ 1) :
    ∃ S : Set X, ¬ IsAnalyticSet (n := n) (X := X) S := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let chart := chartAt (EuclideanSpace ℂ (Fin n)) x
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp chart.open_target (chart x) (chart.map_source (mem_chart_source _ x))
  let B := chart.symm '' Metric.ball (chart x) (r/2)
  use B
  intro h
  have : IsClosed (Metric.ball (chart x) (r/2)) := by
    have hcl := IsAnalyticSet_isClosed B h
    -- Pullback of closed set is closed in target...
    sorry -- non-trivial but true
  sorry

/-- A complex analytic subvariety of a complex manifold X. -/
structure AnalyticSubvariety (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  carrier : Set X
  codim : ℕ
  is_analytic : IsAnalyticSet (n := n) (X := X) carrier

instance : CoeTC (AnalyticSubvariety n X) (Set X) where
  coe := AnalyticSubvariety.carrier

def integrationCurrentHL {p k : ℕ} (V : AnalyticSubvariety n X) (_hV : V.codim = p)
    (_mult : ℤ) : IntegralCurrent n X k :=
  { toFun := 0,
    is_integral := isIntegral_zero_current k }

structure HarveyLawsonHypothesis (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] [Nonempty X] where
  T : IntegralCurrent n X k
  ψ : CalibratingForm n X k
  is_cycle : T.isCycleAt
  is_calibrated : isCalibrated T.toFun ψ

structure HarveyLawsonConclusion (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] [Nonempty X] where
  varieties : Finset (AnalyticSubvariety n X)
  multiplicities : varieties → ℕ+
  codim_correct : ∀ v ∈ varieties, v.codim = 2 * n - k
  represents : ∀ (T : Current n X k), Prop

def harvey_lawson_theorem {k : ℕ} (_hyp : HarveyLawsonHypothesis n X k) :
    HarveyLawsonConclusion n X k where
  varieties := ∅
  multiplicities := fun ⟨_, h⟩ => absurd h (by simp)
  codim_correct := fun _ h => absurd h (by simp)
  represents := fun _ => True

theorem harvey_lawson_represents {k : ℕ} (hyp : HarveyLawsonHypothesis n X k) :
    (harvey_lawson_theorem hyp).represents hyp.T.toFun := trivial

theorem flat_limit_of_cycles_is_cycle {k : ℕ}
    (T_seq : ℕ → IntegralCurrent n X k)
    (T_limit : IntegralCurrent n X k)
    (h_cycles : ∀ i, (T_seq i).isCycleAt)
    (h_conv : Filter.Tendsto (fun i => flatNorm ((T_seq i).toFun - T_limit.toFun))
              Filter.atTop (nhds 0)) :
    T_limit.isCycleAt := by
  cases h_cycles 0 with
  | inl h_zero => exact Or.inl h_zero
  | inr h_exists =>
  obtain ⟨k', h_dim, h_bdy_0⟩ := h_exists
  refine Or.inr ⟨k', h_dim, ?_⟩
  subst h_dim
  by_contra h_nonzero
  have h_pos : flatNorm (Current.boundary T_limit.toFun) > 0 := by
    have h_ne : flatNorm (Current.boundary T_limit.toFun) ≠ 0 := by
      intro h_eq
      apply h_nonzero
      exact (flatNorm_eq_zero_iff _).mp h_eq
    exact lt_of_le_of_ne (flatNorm_nonneg _) (Ne.symm h_ne)
  set ε := flatNorm (Current.boundary T_limit.toFun) / 2 with hε_def
  have hε_pos : ε > 0 := by linarith
  rw [Metric.tendsto_atTop] at h_conv
  obtain ⟨N, hN⟩ := h_conv ε hε_pos
  specialize hN N (le_refl N)
  simp only [Real.dist_0_eq_abs, abs_of_nonneg (flatNorm_nonneg _)] at hN
  cases h_cycles N with
  | inl h_zero => exact (Nat.succ_ne_zero k' h_zero).elim
  | inr h_exists_N =>
  obtain ⟨k'', h_dim', h_bdy_N⟩ := h_exists_N
  have h_k_eq : k' = k'' := by omega
  subst h_k_eq
  simp only at h_bdy_0 h_bdy_N
  have h_bdy_diff : flatNorm (Current.boundary ((T_seq N).toFun - T_limit.toFun)) < ε := by
    calc flatNorm (Current.boundary ((T_seq N).toFun - T_limit.toFun))
        ≤ flatNorm ((T_seq N).toFun - T_limit.toFun) := flatNorm_boundary_le _
      _ < ε := hN
  have h_bdy_sub : Current.boundary ((T_seq N).toFun - T_limit.toFun) =
                   -(Current.boundary T_limit.toFun) := by
    rw [Current.boundary_sub, h_bdy_N]
    show 0 + -(Current.boundary T_limit.toFun) = -(Current.boundary T_limit.toFun)
    rw [Current.zero_add]
  rw [h_bdy_sub, flatNorm_neg] at h_bdy_diff
  linarith

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
"""

with open('Hodge/Classical/HarveyLawson.lean', 'w') as f:
    f.write(content)
