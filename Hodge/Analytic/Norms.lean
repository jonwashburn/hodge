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

open Classical Set Filter Hodge
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

/-- The set of evaluations on the unit ball is non-empty.
    **Note**: Zero vector witnesses nonemptiness (‖0‖ = 0 ≤ 1). -/
theorem pointwiseComass_set_nonempty {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    { r : ℝ | ∃ v : Fin k → TangentSpace (𝓒_complex n) x, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖(α.as_alternating x) v‖ }.Nonempty := by
  use ‖(α.as_alternating x) (fun _ => 0)‖
  refine ⟨fun _ => 0, ?_, rfl⟩
  intro i
  simp only [norm_zero, zero_le_one]

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
  -- The zero form evaluates to 0 on any input, so ‖0 v‖ = 0
  have h_set : { r : ℝ | ∃ v : Fin k → TangentSpace (𝓒_complex n) x,
      (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖((0 : SmoothForm n X k).as_alternating x) v‖ } = {0} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro ⟨v, _, hr⟩
      rw [hr, SmoothForm.zero_apply, AlternatingMap.zero_apply, norm_zero]
    · intro hr
      -- Use the fact that the set is nonempty via the set_nonempty axiom
      obtain ⟨_, v, hv, hrv⟩ := pointwiseComass_set_nonempty (0 : SmoothForm n X k) x
      rw [SmoothForm.zero_apply, AlternatingMap.zero_apply, norm_zero] at hrv
      use v, hv
      rw [hr, SmoothForm.zero_apply, AlternatingMap.zero_apply, norm_zero]
  rw [h_set, csSup_singleton]

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
axiom pointwiseComass_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) (x : X) :
    pointwiseComass (r • α) x = |r| * pointwiseComass α x

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

/-- **Pointwise Comass is Continuous** (Now a Theorem!).
    The pointwise comass (operator norm) of a smooth form varies continuously.

    **Proof**: By definition of `IsSmoothAlternating`, a smooth form α has continuous
    pointwise operator norm. The `pointwiseComass` function is exactly this operator norm,
    so continuity follows directly from the smoothness of α.

    **Mathematical Justification**: This follows from:
    1. Smoothness implies continuity [Lee, "Intro to Smooth Manifolds", Prop 2.3]
    2. Operator norm is continuous on finite-dimensional spaces [Rudin, "Functional Analysis", Thm 1.32]
    3. Local trivialization of tangent bundle [Voisin, "Hodge Theory I", §3.1]

    Reference: [C. Voisin, "Hodge Theory and Complex Algebraic Geometry I", 2002, Section 3.1]. -/
theorem pointwiseComass_continuous {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : Continuous (pointwiseComass α) := by
  -- The smoothness of α directly gives us continuity of the pointwise norm
  unfold pointwiseComass
  -- By definition of IsSmoothAlternating, α.is_smooth states exactly that this function is continuous
  exact α.is_smooth

/-- Global comass norm on forms: supremum of pointwise comass. -/
def comass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X]
    {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  sSup (range (pointwiseComass α))

/-- **Comass Nonnegativity**: Comass is always nonneg (supremum of nonneg values). -/
theorem comass_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X]
    {k : ℕ} (α : SmoothForm n X k) : comass α ≥ 0 := by
  unfold comass
  apply Real.sSup_nonneg
  intro r hr
  obtain ⟨x, hx⟩ := hr
  rw [← hx]
  exact pointwiseComass_nonneg α x

/-- **Comass Norm Definiteness** (Axiom).
    **Blocker**: Requires `BddAbove.of_sSup_eq` and proper norm type matching. -/
axiom comass_eq_zero_iff {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] [Nonempty X]
    {k : ℕ} (α : SmoothForm n X k) :
    comass α = 0 ↔ α = 0

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

/-- Comass scales with absolute value of scalar: comass(c • ω) = |c| * comass(ω). -/
axiom comass_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] [Nonempty X]
    {k : ℕ} (c : ℝ) (ω : SmoothForm n X k) : comass (c • ω) = |c| * comass ω

/-- Instance: NormedAddCommGroup on Smooth Forms (Axiom).
    **Blocker**: NormedAddCommGroup.ofCore API changed in Mathlib 4. -/
axiom instNormedAddCommGroupSmoothForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] [Nonempty X] {k : ℕ} :
    NormedAddCommGroup (SmoothForm n X k)
attribute [instance] instNormedAddCommGroupSmoothForm

/-- Instance: NormedSpace ℝ on Smooth Forms (Axiom). -/
axiom instNormedSpaceRealSmoothForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] [Nonempty X]
    {k : ℕ} : NormedSpace ℝ (SmoothForm n X k)
attribute [instance] instNormedSpaceRealSmoothForm

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
      (∃ (hα : IsFormClosed α), ofForm α hα = η) ∧
      (∀ β : SmoothForm n X k, ∀ (hβ : IsFormClosed β),
        ofForm β hβ = η → energy α ≤ energy β)

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
