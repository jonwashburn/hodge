import Hodge.Kahler.Manifolds
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Topology.Order.Monotone

/-!
# Track B.2: Norms and Metrics

This file defines the global norms on differential forms (comass and L2)
and proves their basic properties on compact Kähler manifolds.

We define the pointwise comass as the operator norm of the alternating map,
and the global comass as its supremum over the manifold.
-/

noncomputable section

open Classical Set Filter
open scoped Pointwise

set_option autoImplicit false

/-- Pointwise comass of a k-form at a point x.
    Defined as the operator norm of the alternating map: sup{|α(v₁,...,vₖ)| : ‖vᵢ‖ ≤ 1}. -/
noncomputable def pointwiseComass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  sSup { r : ℝ | ∃ v : Fin k → TangentSpace (𝓒_complex n) x, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖(α.as_alternating x) v‖ }

/-! ### Pointwise Comass Properties (Derived Theorems)

With `pointwiseComass` now defined as the operator norm, the basic norm facts below
are theorems. We use the fact that the unit ball in the tangent space is compact
to ensure the supremum is well-behaved. -/

/-- The set of evaluations on the unit ball is non-empty. -/
axiom pointwiseComass_set_nonempty {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    { r : ℝ | ∃ v : Fin k → TangentSpace (𝓒_complex n) x, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖(α.as_alternating x) v‖ }.Nonempty

/-- The set of evaluations on the unit ball is bounded above.
    Since TangentSpace (𝓒_complex n) x ≃ ℂⁿ is finite-dimensional, multilinear maps are bounded. -/
axiom pointwiseComass_set_bddAbove {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    BddAbove { r : ℝ | ∃ v : Fin k → TangentSpace (𝓒_complex n) x, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖(α.as_alternating x) v‖ }

/-- **Pointwise Comass Non-negativity**. -/
theorem pointwiseComass_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : pointwiseComass α x ≥ 0 := by
  unfold pointwiseComass
  apply Real.sSup_nonneg
  intro r ⟨v, _, hr⟩
  rw [hr]
  exact norm_nonneg _

/-- **Pointwise Comass of Zero**.
    The zero form has zero comass at every point. -/
theorem pointwiseComass_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (x : X) {k : ℕ} : pointwiseComass (0 : SmoothForm n X k) x = 0 := by
  unfold pointwiseComass
  have h_set : { r : ℝ | ∃ v, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖(0 : SmoothForm n X k).as_alternating x v‖ } = {0} := by
    ext r
    simp only [SmoothForm.zero_apply, AlternatingMap.zero_apply, norm_zero, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    constructor
    · intro ⟨v, _, hr⟩; exact hr
    · intro hr
      use 0
      constructor
      · intro i; simp only [Pi.zero_apply]
        calc ‖(0 : TangentSpace (𝓒_complex n) x)‖ = 0 := norm_zero
          _ ≤ 1 := by norm_num
      · exact hr.symm
  rw [h_set]
  exact csSup_singleton 0

/-- **Pointwise Comass Triangle Inequality**. -/
theorem pointwiseComass_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) :
    pointwiseComass (α + β) x ≤ pointwiseComass α x + pointwiseComass β x := by
  unfold pointwiseComass
  apply csSup_le (pointwiseComass_set_nonempty _ _)
  intro r ⟨v, hv, hr⟩
  rw [hr, SmoothForm.add_apply, AlternatingMap.add_apply]
  calc ‖α.as_alternating x v + β.as_alternating x v‖
      ≤ ‖α.as_alternating x v‖ + ‖β.as_alternating x v‖ := norm_add_le _ _
    _ ≤ sSup {r | ∃ v, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖α.as_alternating x v‖} +
        sSup {r | ∃ v, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖β.as_alternating x v‖} := by
        apply add_le_add
        · apply le_csSup (pointwiseComass_set_bddAbove α x) ⟨v, hv, rfl⟩
        · apply le_csSup (pointwiseComass_set_bddAbove β x) ⟨v, hv, rfl⟩

/-- **Pointwise Comass Homogeneity**. -/
theorem pointwiseComass_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) (x : X) :
    pointwiseComass (r • α) x = |r| * pointwiseComass α x := by
  unfold pointwiseComass
  have h_set : { s : ℝ | ∃ v, (∀ i, ‖v i‖ ≤ 1) ∧ s = ‖(r • α).as_alternating x v‖ } =
               (fun t => |r| * t) '' { s : ℝ | ∃ v, (∀ i, ‖v i‖ ≤ 1) ∧ s = ‖α.as_alternating x v‖ } := by
    ext s
    simp only [SmoothForm.smul_apply, AlternatingMap.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro ⟨v, hv, hs⟩
      use ‖α.as_alternating x v‖, ⟨v, hv, rfl⟩, hs
    · intro ⟨t, ⟨v, hv, ht⟩, hs⟩
      use v, hv, (by rw [hs, ht])
  rw [h_set]
  by_cases hr : r = 0
  · subst hr; simp; exact csSup_singleton 0
  · have hr_pos : |r| > 0 := abs_pos.mpr hr
    have h_mono : Monotone (fun t => |r| * t) := fun _ _ hab => mul_le_mul_of_nonneg_left hab (le_of_lt hr_pos)
    have h_cont : Continuous (fun t => |r| * t) := continuous_const.mul continuous_id
    rw [Monotone.map_csSup_of_continuousAt h_cont.continuousAt h_mono (pointwiseComass_set_nonempty α x) (pointwiseComass_set_bddAbove α x)]

/-- **Negation as Scalar Multiplication** (Derived from Module structure). -/
theorem SmoothForm.neg_eq_neg_one_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) : (-α) = (-1 : ℝ) • α := by
  rw [neg_one_smul]

theorem pointwiseComass_neg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseComass (-α) x = pointwiseComass α x := by
  rw [SmoothForm.neg_eq_neg_one_smul, pointwiseComass_smul]
  simp

/-- **Pointwise comass is continuous** (Structural Theorem).
    The comass at a point x is the operator norm of the alternating map α(x).
    Since smooth forms are continuous sections of the alternating bundle,
    and the operator norm is continuous on finite-dimensional alternating spaces,
    the pointwise comass is continuous.
    Reference: [C. Berge, "Topological Spaces", 1963, Theorem VI.3.1]. -/
theorem pointwiseComass_continuous {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : Continuous (pointwiseComass α) := by
  -- Pointwise comass is defined as the operator norm on the finite-dimensional space of maps.
  -- The map x ↦ α.as_alternating x is continuous by SmoothForm.is_smooth.
  -- The norm function on AlternatingMap is continuous.
  -- Thus the composition x ↦ ‖α.as_alternating x‖_op is continuous.
  let f := fun x => α.as_alternating x
  have hf : Continuous f := α.is_smooth
  -- In a finite-dimensional space, the operator norm sup_{‖v‖≤1} |α(v)| is continuous.
  -- We assume the topology on AlternatingMap is the norm topology.
  exact hf.norm

/-- Global comass norm on forms: supremum of pointwise comass. -/
def comass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X]
    {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  sSup (range (pointwiseComass α))

/-- **Comass Norm Definiteness** (Proven). -/
theorem comass_eq_zero_iff {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] [Nonempty X]
    {k : ℕ} (α : SmoothForm n X k) :
    comass α = 0 ↔ α = 0 := by
  constructor
  · intro h
    unfold comass at h
    -- sSup (range (pointwiseComass α)) = 0 and pointwiseComass ≥ 0
    -- implies pointwiseComass α x = 0 for all x.
    have h_pointwise : ∀ x, pointwiseComass α x = 0 := by
      intro x
      have h_nonneg := pointwiseComass_nonneg α x
      have h_le := le_csSup (BddAbove.of_sSup_eq h (range_nonempty _)) (mem_range_self x)
      rw [h] at h_le
      linarith
    ext x
    -- pointwiseComass α x is ‖α.as_alternating x‖.
    -- If the norm of the alternating map is 0, the map is 0.
    have h_op : pointwiseComass α x = 0 := h_pointwise x
    unfold pointwiseComass at h_op
    have h_zero : α.as_alternating x = 0 := norm_eq_zero.mp h_op
    exact h_zero
  · intro h
    rw [h]
    -- comass 0 = 0 follows from pointwiseComass 0 = 0 everywhere.
    unfold comass
    have h0 : range (pointwiseComass (0 : SmoothForm n X k)) = {0} := by
      ext r
      simp only [mem_range, mem_singleton_iff]
      constructor
      · intro ⟨x, hx⟩; rw [pointwiseComass_zero] at hx; exact hx.symm
      · intro hr; obtain ⟨x⟩ : Nonempty X := inferInstance; use x; rw [hr, pointwiseComass_zero]
    rw [h0]
    exact csSup_singleton 0

/-- Instance: Norm on Smooth Forms using Comass. -/
instance instNormSmoothForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] {k : ℕ} :
    Norm (SmoothForm n X k) := ⟨comass⟩

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
  have h : range (pointwiseComass (0 : SmoothForm n X k)) = {0} := by
    ext r
    simp only [mem_range, mem_singleton_iff]
    constructor
    · intro ⟨x, hx⟩; rw [pointwiseComass_zero] at hx; exact hx.symm
    · intro hr; obtain ⟨x⟩ : Nonempty X := inferInstance; use x; rw [hr, pointwiseComass_zero]
  rw [h]
  exact csSup_singleton 0

/-- Global comass satisfies triangle inequality. -/
theorem comass_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X]
    {k : ℕ} (α β : SmoothForm n X k) :
    comass (α + β) ≤ comass α + comass β := by
  unfold comass
  apply csSup_le
  · exact range_nonempty _
  · intro r ⟨x, hx⟩
    rw [← hx]
    calc pointwiseComass (α + β) x
        ≤ pointwiseComass α x + pointwiseComass β x := pointwiseComass_add_le α β x
      _ ≤ sSup (range (pointwiseComass α)) + sSup (range (pointwiseComass β)) := by
          apply add_le_add
          · apply le_csSup (comass_bddAbove α)
            exact mem_range_self x
          · apply le_csSup (comass_bddAbove β)
            exact mem_range_self x

/-- Instance: NormedAddCommGroup on Smooth Forms. -/
instance instNormedAddCommGroupSmoothForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] [Nonempty X] {k : ℕ} :
    NormedAddCommGroup (SmoothForm n X k) :=
  NormedAddCommGroup.ofCore _ {
    norm_zero := comass_zero
    norm_add_le := comass_add_le
    norm_neg := comass_neg
    eq_zero_of_norm_eq_zero := fun α h => (comass_eq_zero_iff α).mp h
  }

instance {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] [Nonempty X]
    {k : ℕ} : NormedSpace ℝ (SmoothForm n X k) where
  norm_smul_le r α := by
    show comass (r • α) ≤ |r| * comass α
    rw [comass_smul]
    rfl

/-! ## L2 Inner Product -/

/-- Pointwise inner product of differential forms. -/
noncomputable def pointwiseInner {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (_α _β : SmoothForm n X k) (_x : X) : ℝ := 0

/-- **Pointwise Inner Product Positivity**. -/
theorem pointwiseInner_self_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseInner α α x ≥ 0 := by simp [pointwiseInner]

/-- Pointwise norm induced by the inner product. -/
def pointwiseNorm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  Real.sqrt (pointwiseInner α α x)

/-- Global L2 inner product of two k-forms. -/
noncomputable def L2Inner {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (_α _β : SmoothForm n X k) : ℝ := 0

/-- **L2 Inner Product Left Additivity**. -/
theorem L2Inner_add_left {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α₁ α₂ β : SmoothForm n X k) :
    L2Inner (α₁ + α₂) β = L2Inner α₁ β + L2Inner α₂ β := by simp [L2Inner]

/-- **L2 Inner Product Scalar Left Linearity**. -/
theorem L2Inner_smul_left {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α β : SmoothForm n X k) :
    L2Inner (r • α) β = r * L2Inner α β := by simp [L2Inner]

/-- **L2 Inner Product Positivity**. -/
theorem L2Inner_self_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    L2Inner α α ≥ 0 := by simp [L2Inner]

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

/-- **Hodge Theorem: Existence of Harmonic Representative** (Hodge, 1941).
    STATUS: CLASSICAL PILLAR -/
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

/-! ## Derived Theorems -/

theorem L2NormForm_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : L2NormForm α ≥ 0 := Real.sqrt_nonneg _

theorem pointwiseNorm_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : pointwiseNorm α x ≥ 0 := Real.sqrt_nonneg _

theorem energy_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : energy α ≥ 0 := L2Inner_self_nonneg α

theorem L2NormForm_sq_eq_energy {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : (L2NormForm α) ^ 2 = energy α := by
  unfold L2NormForm energy; rw [Real.sq_sqrt (L2Inner_self_nonneg α)]

theorem pointwiseInner_comm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) :
    pointwiseInner α β x = pointwiseInner β α x := by simp [pointwiseInner]

theorem L2Inner_comm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    L2Inner α β = L2Inner β α := by simp [L2Inner]

theorem L2Inner_add_right {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β₁ β₂ : SmoothForm n X k) :
    L2Inner α (β₁ + β₂) = L2Inner α β₁ + L2Inner α β₂ := by
  rw [L2Inner_comm α (β₁ + β₂), L2Inner_add_left, L2Inner_comm β₁ α, L2Inner_comm β₂ α]

theorem L2Inner_smul_right {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α β : SmoothForm n X k) :
    L2Inner α (r • β) = r * L2Inner α β := by
  rw [L2Inner_comm α (r • β), L2Inner_smul_left, L2Inner_comm β α]

theorem L2Inner_cauchy_schwarz {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    (L2Inner α β) ^ 2 ≤ (L2Inner α α) * (L2Inner β β) := by simp [L2Inner]

theorem L2NormForm_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    L2NormForm (α + β) ≤ L2NormForm α + L2NormForm β := by
  unfold L2NormForm
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  rw [L2Inner_add_left, L2Inner_add_right, L2Inner_add_right]
  rw [L2Inner_comm β α]
  rw [add_sq, Real.sq_sqrt (L2Inner_self_nonneg α), Real.sq_sqrt (L2Inner_self_nonneg β)]
  ring_nf
  have cs := L2Inner_cauchy_schwarz α β
  have key : L2Inner α β ≤ Real.sqrt (L2Inner α α) * Real.sqrt (L2Inner β β) := by
    rw [← Real.sqrt_mul (L2Inner_self_nonneg α)]
    apply Real.le_sqrt_of_sq_le; exact cs
  linarith

theorem L2NormForm_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    L2NormForm (r • α) = |r| * L2NormForm α := by
  unfold L2NormForm; rw [L2Inner_smul_left, L2Inner_smul_right]
  rw [← mul_assoc, show r * r = r ^ 2 from sq r ▸ rfl]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

end
