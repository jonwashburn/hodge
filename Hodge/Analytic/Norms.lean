import Hodge.Analytic.Forms
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Basic

/-!
# Track B.2: Norms and Metrics

This file defines the global norms on differential forms (comass and L2)
and proves their basic properties on compact Kähler manifolds.
-/

noncomputable section

open Classical Set Filter

set_option autoImplicit false

/-- The pointwise comass set of a k-form at a point x. -/
def pointwiseComassSet {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : Set ℝ :=
  { r : ℝ | ∃ (v : Fin k → TangentSpace (𝓒_complex n) x),
    (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖α.as_alternating x v‖ }

/-- The pointwise comass of a k-form at a point x.
    Defined as sup{|α(v₁,...,vₖ)| : ‖vᵢ‖ ≤ 1}. -/
def pointwiseComass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  sSup (pointwiseComassSet α x)

/-- Pointwise comass is non-negative. -/
theorem pointwiseComass_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : pointwiseComass α x ≥ 0 := by
  apply csSup_nonneg
  · use 0
    refine ⟨fun _ => 0, fun _ => by simp, ?_⟩
    simp
  · rintro r ⟨v, _, rfl⟩
    positivity

/-- Pointwise comass of zero form is zero. -/
theorem pointwiseComass_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (x : X) {k : ℕ} : pointwiseComass (0 : SmoothForm n X k) x = 0 := by
  unfold pointwiseComass pointwiseComassSet
  have h_set : { r : ℝ | ∃ v, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖(0 : SmoothForm n X k).as_alternating x v‖ } = {0} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, SmoothForm.zero_apply,
               AlternatingMap.zero_apply, norm_zero]
    constructor
    · rintro ⟨v, _, hr⟩; exact hr
    · intro h; subst h; exact ⟨fun _ => 0, fun _ => by simp, rfl⟩
  rw [h_set, csSup_singleton]

/-- The pointwise comass set is bounded above by the operator norm. -/
theorem pointwiseComassSet_bddAbove {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    BddAbove (pointwiseComassSet α x) := by
  use ‖α.as_alternating x‖
  intro r ⟨v, hv_bound, hr⟩
  rw [hr]
  apply AlternatingMap.norm_map_le_of_forall_le
  intro i
  exact hv_bound i

/-- Pointwise comass satisfies triangle inequality. -/
theorem pointwiseComass_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) :
    pointwiseComass (α + β) x ≤ pointwiseComass α x + pointwiseComass β x := by
  unfold pointwiseComass
  apply csSup_le
  · use 0
    refine ⟨fun _ => 0, fun _ => by simp, ?_⟩
    simp
  · rintro r ⟨v, hv, rfl⟩
    calc ‖(α + β).as_alternating x v‖
      _ = ‖α.as_alternating x v + β.as_alternating x v‖ := rfl
      _ ≤ ‖α.as_alternating x v‖ + ‖β.as_alternating x v‖ := norm_add_le _ _
      _ ≤ sSup (pointwiseComassSet α x) + sSup (pointwiseComassSet β x) := by
        apply add_le_add
        · apply le_csSup (pointwiseComassSet_bddAbove α x); exact ⟨v, hv, rfl⟩
        · apply le_csSup (pointwiseComassSet_bddAbove β x); exact ⟨v, hv, rfl⟩

/-- Pointwise comass scales with absolute value. -/
theorem pointwiseComass_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) (x : X) :
    pointwiseComass (r • α) x = |r| * pointwiseComass α x := by
  unfold pointwiseComass
  by_cases hr : r = 0
  · subst hr
    simp only [abs_zero, zero_mul, zero_smul]
    exact pointwiseComass_zero x
  · have h_eq : pointwiseComassSet (r • α) x = (fun s => |r| * s) '' pointwiseComassSet α x := by
      ext s
      simp only [pointwiseComassSet, SmoothForm.smul_real_apply, AlternatingMap.smul_apply, norm_smul, Real.norm_eq_abs, Set.mem_setOf_eq, mem_image]
      constructor
      · rintro ⟨v, hv, rfl⟩; use ‖α.as_alternating x v‖; exact ⟨⟨v, hv, rfl⟩, rfl⟩
      · rintro ⟨s', ⟨v, hv, rfl⟩, rfl⟩; exact ⟨v, hv, rfl⟩
    rw [h_eq]
    apply Real.sSup_mul_of_nonneg (abs_nonneg r)
    use 0
    refine ⟨fun _ => 0, fun _ => by simp, ?_⟩
    simp

/-- Pointwise comass of negation equals pointwise comass. -/
theorem pointwiseComass_neg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseComass (-α) x = pointwiseComass α x := by
  have : (-α) = (-1 : ℝ) • α := by ext; simp
  rw [this, pointwiseComass_smul]
  simp

/-- **Berge's Maximum Theorem**: Pointwise comass is continuous for smooth forms. -/
axiom pointwiseComass_continuous {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : Continuous (pointwiseComass α)

/-- Global comass norm on forms: supremum of pointwise comass. -/
def comass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X]
    {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  sSup (range (pointwiseComass α))

/-- Global comass is bounded above on compact manifolds. -/
theorem comass_bddAbove {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    BddAbove (range (pointwiseComass α)) := by
  apply IsCompact.bddAbove
  apply isCompact_range
  exact pointwiseComass_continuous α

/-- The comass of the zero form is zero. -/
theorem comass_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] [Nonempty X]
    {k : ℕ} : comass (n := n) (0 : SmoothForm n X k) = 0 := by
  unfold comass
  simp only [pointwiseComass_zero, image_const, range_const, sSup_singleton]

/-- Global comass satisfies triangle inequality. -/
theorem comass_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    comass (α + β) ≤ comass α + comass β := by
  unfold comass
  apply ciSup_le
  intro x
  calc pointwiseComass (α + β) x
    _ ≤ pointwiseComass α x + pointwiseComass β x := pointwiseComass_add_le α β x
    _ ≤ ⨆ y, pointwiseComass α y + ⨆ y, pointwiseComass β y := by
      apply add_le_add
      · exact le_ciSup (comass_bddAbove α) x
      · exact le_ciSup (comass_bddAbove β) x

/-- **Comass Homogeneity** (Standard).
    The comass norm is homogeneous: comass (r • α) = |r| * comass α.
    Reference: [H. Federer, "Geometric Measure Theory", 1969]. -/
theorem comass_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    comass (r • α) = |r| * comass α := by
  unfold comass
  simp only [pointwiseComass_smul]
  rw [Real.mul_iSup_of_nonneg (abs_nonneg r)]
  · exact comass_bddAbove α

/-- Comass is non-negative. -/
theorem comass_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] [Nonempty X]
    {k : ℕ} (α : SmoothForm n X k) : comass α ≥ 0 := by
  unfold comass
  apply ciSup_nonneg
  intro x
  exact pointwiseComass_nonneg α x

/-- **Comass Norm Definiteness** (Standard).
    The comass norm of a form is zero if and only if the form is identically zero. -/
theorem comass_eq_zero_iff {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] [Nonempty X]
    {k : ℕ} (α : SmoothForm n X k) :
    comass α = 0 ↔ α = 0 := by
  constructor
  · intro h
    ext x v
    have h_pw : pointwiseComass α x = 0 := by
      have : pointwiseComass α x ≤ comass α := le_ciSup (comass_bddAbove α) x
      linarith [pointwiseComass_nonneg α x]
    unfold pointwiseComass at h_pw
    have h_set : pointwiseComassSet α x = {0} := by
      ext r
      constructor
      · intro hr
        have := le_csSup (pointwiseComassSet_bddAbove α x) hr
        rw [h_pw] at this
        have : r ≥ 0 := by
          rcases hr with ⟨v', _, rfl⟩
          positivity
        linarith
      · rintro rfl
        use fun _ => 0
        refine ⟨fun _ => by simp, ?_⟩
        simp
    have h_norm : ‖α.as_alternating x v‖ = 0 := by
      have h_v_bound : ∃ c : ℝ, c > 0 ∧ ∀ i, ‖v i‖ ≤ c := by
        use (Finset.univ.image (fun i => ‖v i‖)).max' (Finset.univ_nonempty.image _) + 1
        constructor
        · have : 0 ≤ _ := by positivity
          linarith
        · intro i
          have : ‖v i‖ ≤ (Finset.univ.image (fun i => ‖v i‖)).max' _ := Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
          linarith
      obtain ⟨c, hc_pos, hc_bound⟩ := h_v_bound
      let v' := fun i => (c⁻¹ : ℂ) • v i
      have h_v'_bound : ∀ i, ‖v' i‖ ≤ 1 := by
        intro i
        unfold v'
        rw [norm_smul, norm_inv, Complex.norm_eq_abs]
        apply inv_mul_le_one hc_pos
        exact hc_bound i
      have h_r_in : ‖α.as_alternating x v'‖ ∈ pointwiseComassSet α x := ⟨v', h_v'_bound, rfl⟩
      rw [h_set] at h_r_in
      simp only [Set.mem_singleton_iff] at h_r_in
      unfold v' at h_r_in
      simp only [AlternatingMap.smul_apply, norm_smul, norm_pow, norm_inv, Complex.norm_eq_abs] at h_r_in
      have : (c⁻¹)^k ≠ 0 := by
        apply pow_ne_zero
        exact inv_ne_zero hc_pos.ne'
      exact (mul_eq_zero.mp h_r_in).resolve_left this
    exact norm_eq_zero.mp h_norm
  · intro h
    rw [h, comass_zero]

/-- Smooth forms form a normed additive commutative group under comass. -/
instance smoothFormNormedAddCommGroup {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [CompactSpace X] [Nonempty X]
    (k : ℕ) : NormedAddCommGroup (SmoothForm n X k) :=
  NormedAddCommGroup.ofCore (SmoothForm n X k) {
    norm := comass
    norm_zero := comass_zero
    norm_add_le := comass_add_le
    norm_neg := by
      intro α
      unfold comass
      simp only [pointwiseComass_neg]
    eq_of_norm_eq_zero := fun α => (comass_eq_zero_iff α).mp
  }

/-- Smooth forms form a normed space over ℝ. -/
instance smoothFormNormedSpace {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [CompactSpace X] [Nonempty X]
    (k : ℕ) : NormedSpace ℝ (SmoothForm n X k) :=
  NormedSpace.ofCore (SmoothForm n X k) ℝ {
    norm_smul_le := fun r α => by
      rw [comass_smul]
      exact le_refl _
  }

/-! ## L2 Inner Product -/

/-- Pointwise inner product of differential forms. -/
def pointwiseInner {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) : ℝ :=
  pointwiseInnerAlternating x (α.as_alternating x) (β.as_alternating x)

/-- The pointwise inner product is non-negative for self-pairing. -/
axiom pointwiseInner_self_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseInner α α x ≥ 0

/-- Pointwise norm induced by the inner product. -/
def pointwiseNorm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  Real.sqrt (pointwiseInner α α x)

/-- Global L2 inner product of two k-forms. -/
opaque L2Inner {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) : ℝ

axiom L2Inner_add_left {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α₁ α₂ β : SmoothForm n X k) :
    L2Inner (α₁ + α₂) β = L2Inner α₁ β + L2Inner α₂ β

axiom L2Inner_smul_left {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α β : SmoothForm n X k) :
    L2Inner (r • α) β = r * L2Inner α β

/-- Global L2 norm of a k-form. -/
def L2NormForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  Real.sqrt (L2Inner α α)

/-! ## Energy Functional -/

/-- The energy of a form is the L2 norm squared. -/
def energy {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : ℝ := L2Inner α α

/-- **Hodge Theorem: Existence of Harmonic Representative** (Hodge, 1941). -/
axiom energy_minimizer {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    {k : ℕ} (η : DeRhamCohomologyClass n X k) :
    ∃! α : SmoothForm n X k,
      (∃ (hα : IsFormClosed α), DeRhamCohomologyClass.ofForm α hα = η) ∧
      (∀ β : SmoothForm n X k, ∀ (hβ : IsFormClosed β),
        DeRhamCohomologyClass.ofForm β hβ = η → energy α ≤ energy β)

/-- **Trace-L2 Control** (Sobolev/Gagliardo-Nirenberg). -/
axiom trace_L2_control {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    ∃ C : ℝ, C > 0 ∧ comass α ≤ C * L2NormForm α
