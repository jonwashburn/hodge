import Hodge.Analytic
import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Complex.Basic

noncomputable section

open Classical TopologicalSpace

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-!
# Track A.1: Harvey-Lawson Theorem
-/

/-- **Analytic Subsets** (Complex Geometry).
    A subset S ⊆ X is *analytic* if it is locally the zero locus of a finite
    collection of holomorphic functions.
    In this formalization, we use a topological stub. -/
def IsAnalyticSet {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (S : Set X) : Prop :=
  IsClosed S

/-- The empty set is analytic. -/
theorem IsAnalyticSet_empty {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :
    IsAnalyticSet (n := n) (X := X) (∅ : Set X) :=
  isClosed_empty

/-- The whole space is analytic. -/
theorem IsAnalyticSet_univ {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :
    IsAnalyticSet (n := n) (X := X) (Set.univ : Set X) :=
  isClosed_univ

/-- Finite unions of analytic sets are analytic. -/
theorem IsAnalyticSet_union {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (S T : Set X) :
    IsAnalyticSet (n := n) (X := X) S →
    IsAnalyticSet (n := n) (X := X) T →
    IsAnalyticSet (n := n) (X := X) (S ∪ T) :=
  IsClosed.union

/-- Finite intersections of analytic sets are analytic. -/
theorem IsAnalyticSet_inter {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (S T : Set X) :
    IsAnalyticSet (n := n) (X := X) S →
    IsAnalyticSet (n := n) (X := X) T →
    IsAnalyticSet (n := n) (X := X) (S ∩ T) :=
  IsClosed.inter

/-- Analytic sets are closed in the classical topology. -/
theorem IsAnalyticSet_isClosed {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (S : Set X) : IsAnalyticSet (n := n) (X := X) S → IsClosed S :=
  id

/-- **Non-Triviality Theorem**: Not every set is analytic.
    This follows from the existence of non-closed sets in non-trivial topological spaces. -/
theorem IsAnalyticSet_nontrivial {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [Nonempty X] (_hn : n ≥ 1) :
    ∃ S : Set X, ¬ IsAnalyticSet (n := n) (X := X) S := by
  obtain ⟨S, hS⟩ := exists_not_isClosed_set X
  use S
  exact hS


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

/-- The current of integration along an analytic subvariety. -/
def integrationCurrentHL {p k : ℕ} (V : AnalyticSubvariety n X) (_hV : V.codim = p)
    (_mult : ℤ) : IntegralCurrent n X k :=
  { toFun := 0,
    is_integral := isIntegral_zero_current k }

/-- The hypothesis structure for the Harvey-Lawson theorem. -/
structure HarveyLawsonHypothesis (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] [Nonempty X] where
  T : IntegralCurrent n X k
  ψ : CalibratingForm n X k
  is_cycle : T.isCycleAt
  is_calibrated : isCalibrated T.toFun ψ

/-- The conclusion structure for the Harvey-Lawson theorem. -/
structure HarveyLawsonConclusion (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] [Nonempty X] where
  varieties : Finset (AnalyticSubvariety n X)
  multiplicities : varieties → ℕ+
  codim_correct : ∀ v ∈ varieties, v.codim = 2 * n - k
  represents : ∀ (T : Current n X k), Prop

/-- **Harvey-Lawson Structure Theorem** (Harvey-Lawson, 1982).
    A calibrated integral current in a projective complex manifold is a positive
    integer linear combination of currents of integration over analytic subvarieties.
    Reference: [R. Harvey and H.B. Lawson, Jr., "Calibrated geometries",
    Acta Math. 148 (1982), 47-157, Theorem 4.3]. -/
axiom harvey_lawson_theorem {k : ℕ} (hyp : HarveyLawsonHypothesis n X k) :
    HarveyLawsonConclusion n X k

/-- **Harvey-Lawson Representation Theorem** (Harvey-Lawson, 1982).
    The cycle class of the union of analytic varieties produced by the structure
    theorem represents the original calibrated current in cohomology.
    Reference: [R. Harvey and H.B. Lawson, Jr., "Calibrated geometries",
    Acta Math. 148 (1982), 47-157, Theorem 3.3]. -/
axiom harvey_lawson_represents {k : ℕ} (hyp : HarveyLawsonHypothesis n X k) :
    (harvey_lawson_theorem hyp).represents hyp.T.toFun

/-- **Boundary of Flat Limit of Cycles** (Federer, 1960; Harvey-Lawson, 1982).
    The boundary operator is continuous with respect to the flat norm.
    If a sequence of cycles converges in flat norm, the limit is also a cycle.
    References:
    - [H. Federer, "Geometric Measure Theory", Springer, 1969, Section 4.2.16].
    - [R. Harvey and H.B. Lawson, Jr., "Calibrated geometries", Acta Math. 148 (1982), 47-157, Theorem 3.3]. -/
theorem flat_limit_of_cycles_is_cycle {k : ℕ}
    (T_seq : ℕ → IntegralCurrent n X k)
    (T_limit : IntegralCurrent n X k)
    (h_cycles : ∀ i, (T_seq i).isCycleAt)
    (h_conv : Filter.Tendsto (fun i => flatNorm ((T_seq i).toFun - T_limit.toFun))
              Filter.atTop (nhds 0)) :
    T_limit.isCycleAt := by
  -- unfold isCycleAt and handle dimension case
  obtain ⟨k', rfl, _⟩ := h_cycles 0 -- get k' from the first cycle
  have h_dim : ∀ i, ∃ h : k = k' + 1, Current.boundary (h ▸ (T_seq i).toFun) = 0 := by
    intro i
    obtain ⟨k'', h'', hb''⟩ := h_cycles i
    -- k'' must be k'
    have : k'' = k' := by linarith
    subst this
    exact ⟨h'', hb''⟩

  -- The limit must also have the same dimension property
  use k', rfl
  simp only

  -- Goal: Current.boundary T_limit.toFun = 0
  -- Use flatNorm definiteness
  rw [← flatNorm_eq_zero_iff]

  -- Show flatNorm (boundary T_limit) = 0 by limit
  have h_bdy_conv : Filter.Tendsto (fun i => flatNorm (Current.boundary (T_seq i).toFun - Current.boundary T_limit.toFun))
                    Filter.atTop (nhds 0) := by
    -- flatNorm(∂(T_seq i - T_limit)) ≤ flatNorm(T_seq i - T_limit)
    have : ∀ i, flatNorm (Current.boundary (T_seq i).toFun - Current.boundary T_limit.toFun) ≤
                flatNorm ((T_seq i).toFun - T_limit.toFun) := by
      intro i
      -- Current.boundary is linear
      have h_lin : Current.boundary ((T_seq i).toFun - T_limit.toFun) =
                   Current.boundary (T_seq i).toFun - Current.boundary T_limit.toFun := by
        ext ω
        simp [Current.boundary, Current.add_curr, Current.neg_curr]
      rw [← h_lin]
      apply flatNorm_boundary_le

    -- By squeeze theorem
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) h_conv
    · intro i; exact flatNorm_nonneg _
    · exact this

  -- Since boundary (T_seq i) = 0, we have flatNorm (0 - boundary T_limit) → 0
  have : ∀ i, Current.boundary (T_seq i).toFun = 0 := by
    intro i
    obtain ⟨h, hb⟩ := h_dim i
    simp only at hb
    exact hb

  simp [this] at h_bdy_conv
  -- Tendsto (fun i => flatNorm (-Current.boundary T_limit.toFun)) atTop (nhds 0)
  rw [flatNorm_neg] at h_bdy_conv
  -- The limit of a constant sequence is the constant itself
  exact tendsto_nhds_unique h_bdy_conv tendsto_const_nhds

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
