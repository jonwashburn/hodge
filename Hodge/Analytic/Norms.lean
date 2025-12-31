import Hodge.Analytic.Forms
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Track B.2: Norms and Metrics

This file defines the global norms on differential forms (comass and L2)
and proves their basic properties on compact Kähler manifolds.

Since `SmoothForm` is opaque, we axiomatize the key properties of the pointwise
comass and L2 norms rather than proving them from first principles.
-/

noncomputable section

open Classical Set Filter

set_option autoImplicit false

/-- Pointwise comass of a k-form at a point x.
    Defined abstractly as sup{|α(v₁,...,vₖ)| : ‖vᵢ‖ ≤ 1}. -/
opaque pointwiseComass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ

-- Axiomatize the key properties of pointwise comass
axiom pointwiseComass_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : pointwiseComass α x ≥ 0

axiom pointwiseComass_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) :
    pointwiseComass (α + β) x ≤ pointwiseComass α x + pointwiseComass β x

axiom pointwiseComass_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) (x : X) :
    pointwiseComass (r • α) x = |r| * pointwiseComass α x

/-- Pointwise comass of zero is zero (derived from smul). -/
theorem pointwiseComass_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (x : X) {k : ℕ} : pointwiseComass (0 : SmoothForm n X k) x = 0 := by
  have h : (0 : SmoothForm n X k) = (0 : ℝ) • (0 : SmoothForm n X k) := by simp
  rw [h, pointwiseComass_smul]
  simp

-- Axiom: Negation equals scalar multiplication by -1 (for opaque SmoothForm)
axiom SmoothForm.neg_eq_neg_one_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) : (-α) = (-1 : ℝ) • α

theorem pointwiseComass_neg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseComass (-α) x = pointwiseComass α x := by
  rw [SmoothForm.neg_eq_neg_one_smul, pointwiseComass_smul]
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
  -- The range of pointwiseComass 0 is {0} since pointwiseComass_zero says it's 0 everywhere
  have h : range (pointwiseComass (0 : SmoothForm n X k)) = {0} := by
    ext r
    simp only [mem_range, mem_singleton_iff]
    constructor
    · intro ⟨x, hx⟩
      rw [pointwiseComass_zero] at hx
      exact hx.symm
    · intro hr
      obtain ⟨x⟩ : Nonempty X := inferInstance
      use x
      rw [hr, pointwiseComass_zero]
  rw [h]
  exact csSup_singleton 0

/-- Global comass satisfies triangle inequality. -/
axiom comass_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    comass (α + β) ≤ comass α + comass β

/-- **Comass Homogeneity** (Standard).
    The comass norm is homogeneous: comass (r • α) = |r| * comass α.
    Reference: [H. Federer, "Geometric Measure Theory", 1969].
    This follows from pointwiseComass_smul and properties of sSup. -/
axiom comass_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    comass (r • α) = |r| * comass α

/-- Comass is non-negative (derived from pointwiseComass_nonneg). -/
theorem comass_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : comass α ≥ 0 := by
  unfold comass
  apply Real.sSup_nonneg
  intro r ⟨x, hx⟩
  rw [← hx]
  exact pointwiseComass_nonneg α x

/-- Comass of negation equals comass (derived from smul and neg_eq). -/
theorem comass_neg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    comass (-α) = comass α := by
  rw [SmoothForm.neg_eq_neg_one_smul, comass_smul]
  simp

/-- **Comass Norm Definiteness** (Standard).
    The comass norm of a form is zero if and only if the form is identically zero. -/
axiom comass_eq_zero_iff {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] [Nonempty X]
    {k : ℕ} (α : SmoothForm n X k) :
    comass α = 0 ↔ α = 0

/-! ## L2 Inner Product -/

/-- Pointwise inner product of differential forms. -/
opaque pointwiseInner {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) : ℝ

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

axiom L2Inner_self_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    L2Inner α α ≥ 0

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

/-! ## Derived Theorems -/

/-- L2 norm is non-negative (derived from L2Inner_self_nonneg). -/
theorem L2NormForm_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : L2NormForm α ≥ 0 := by
  unfold L2NormForm
  exact Real.sqrt_nonneg _

/-- Pointwise norm is non-negative (derived from pointwiseInner_self_nonneg). -/
theorem pointwiseNorm_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : pointwiseNorm α x ≥ 0 := by
  unfold pointwiseNorm
  exact Real.sqrt_nonneg _

/-- Energy is non-negative (derived from L2Inner_self_nonneg). -/
theorem energy_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : energy α ≥ 0 := by
  unfold energy
  exact L2Inner_self_nonneg α

/-- L2 norm squared equals energy. -/
theorem L2NormForm_sq_eq_energy {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : (L2NormForm α) ^ 2 = energy α := by
  unfold L2NormForm energy
  rw [Real.sq_sqrt (L2Inner_self_nonneg α)]

/-- Pointwise inner product is symmetric. -/
axiom pointwiseInner_comm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) :
    pointwiseInner α β x = pointwiseInner β α x

/-- L2 inner product is symmetric. -/
axiom L2Inner_comm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    L2Inner α β = L2Inner β α

/-- L2 inner product is right-additive (derived from symmetry and left-additivity). -/
theorem L2Inner_add_right {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β₁ β₂ : SmoothForm n X k) :
    L2Inner α (β₁ + β₂) = L2Inner α β₁ + L2Inner α β₂ := by
  rw [L2Inner_comm α (β₁ + β₂), L2Inner_add_left, L2Inner_comm β₁ α, L2Inner_comm β₂ α]

/-- L2 inner product is right ℝ-linear. -/
theorem L2Inner_smul_right {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α β : SmoothForm n X k) :
    L2Inner α (r • β) = r * L2Inner α β := by
  rw [L2Inner_comm α (r • β), L2Inner_smul_left, L2Inner_comm β α]

/-- L2 inner product with zero on left. -/
theorem L2Inner_zero_left {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (β : SmoothForm n X k) :
    L2Inner (0 : SmoothForm n X k) β = 0 := by
  have h := L2Inner_smul_left (0 : ℝ) (0 : SmoothForm n X k) β
  simp at h
  exact h

/-- L2 inner product with zero on right. -/
theorem L2Inner_zero_right {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    L2Inner α (0 : SmoothForm n X k) = 0 := by
  rw [L2Inner_comm, L2Inner_zero_left]

/-- L2 inner product with negation on left. -/
theorem L2Inner_neg_left {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    L2Inner (-α) β = -L2Inner α β := by
  rw [SmoothForm.neg_eq_neg_one_smul, L2Inner_smul_left]
  ring

/-- L2 inner product with negation on right. -/
theorem L2Inner_neg_right {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    L2Inner α (-β) = -L2Inner α β := by
  rw [L2Inner_comm, L2Inner_neg_left, L2Inner_comm]

/-- L2 norm of zero is zero. -/
theorem L2NormForm_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} : L2NormForm (0 : SmoothForm n X k) = 0 := by
  unfold L2NormForm
  rw [L2Inner_zero_left]
  simp

/-- L2 norm of negation equals L2 norm. -/
theorem L2NormForm_neg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : L2NormForm (-α) = L2NormForm α := by
  unfold L2NormForm
  have h1 : L2Inner (-α) (-α) = -L2Inner α (-α) := L2Inner_neg_left α (-α)
  have h2 : L2Inner α (-α) = -L2Inner α α := L2Inner_neg_right α α
  rw [h1, h2]
  ring_nf

/-- Cauchy-Schwarz inequality for L2 inner product. -/
axiom L2Inner_cauchy_schwarz {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    (L2Inner α β) ^ 2 ≤ (L2Inner α α) * (L2Inner β β)

/-- Triangle inequality for L2 norm (derived from Cauchy-Schwarz).
    Standard proof: ‖α + β‖² = ⟨α,α⟩ + 2⟨α,β⟩ + ⟨β,β⟩ ≤ (‖α‖ + ‖β‖)² -/
theorem L2NormForm_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    L2NormForm (α + β) ≤ L2NormForm α + L2NormForm β := by
  -- Expand ⟨α+β, α+β⟩ = ⟨α,α⟩ + 2⟨α,β⟩ + ⟨β,β⟩
  have h_sq : L2Inner (α + β) (α + β) = L2Inner α α + 2 * L2Inner α β + L2Inner β β := by
    rw [L2Inner_add_left, L2Inner_add_right, L2Inner_add_right, L2Inner_comm β α]; ring
  -- ‖α‖² = ⟨α,α⟩
  have h_norm_sq_α : (L2NormForm α) ^ 2 = L2Inner α α := by
    unfold L2NormForm; rw [Real.sq_sqrt (L2Inner_self_nonneg α)]
  have h_norm_sq_β : (L2NormForm β) ^ 2 = L2Inner β β := by
    unfold L2NormForm; rw [Real.sq_sqrt (L2Inner_self_nonneg β)]
  -- Cauchy-Schwarz: (⟨α,β⟩)² ≤ ⟨α,α⟩⟨β,β⟩ = ‖α‖²‖β‖² = (‖α‖‖β‖)²
  have hcs := L2Inner_cauchy_schwarz α β
  have hcs' : (L2Inner α β) ^ 2 ≤ (L2NormForm α * L2NormForm β) ^ 2 := by
    calc (L2Inner α β) ^ 2 ≤ L2Inner α α * L2Inner β β := hcs
         _ = (L2NormForm α) ^ 2 * (L2NormForm β) ^ 2 := by rw [h_norm_sq_α, h_norm_sq_β]
         _ = (L2NormForm α * L2NormForm β) ^ 2 := by ring
  have hprod_nonneg : 0 ≤ L2NormForm α * L2NormForm β :=
    mul_nonneg (L2NormForm_nonneg α) (L2NormForm_nonneg β)
  -- From x² ≤ y² and y ≥ 0, get |x| ≤ y, hence x ≤ y
  have h_ab_bound : L2Inner α β ≤ L2NormForm α * L2NormForm β := by
    have hab : |L2Inner α β| ≤ L2NormForm α * L2NormForm β := by
      rw [← Real.sqrt_sq hprod_nonneg, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hcs'
    exact le_trans (le_abs_self _) hab
  -- ‖α+β‖² ≤ (‖α‖ + ‖β‖)²
  have h_ineq : L2Inner (α + β) (α + β) ≤ (L2NormForm α + L2NormForm β) ^ 2 := by
    rw [h_sq]
    have h_rhs : (L2NormForm α + L2NormForm β) ^ 2 =
        (L2NormForm α) ^ 2 + 2 * (L2NormForm α * L2NormForm β) + (L2NormForm β) ^ 2 := by ring
    rw [h_rhs, h_norm_sq_α, h_norm_sq_β]
    linarith [h_ab_bound]
  -- Take sqrt
  have h_sum_nonneg : 0 ≤ L2NormForm α + L2NormForm β :=
    add_nonneg (L2NormForm_nonneg α) (L2NormForm_nonneg β)
  unfold L2NormForm
  calc Real.sqrt (L2Inner (α + β) (α + β))
       ≤ Real.sqrt ((L2NormForm α + L2NormForm β) ^ 2) := Real.sqrt_le_sqrt h_ineq
     _ = L2NormForm α + L2NormForm β := Real.sqrt_sq h_sum_nonneg
     _ = Real.sqrt (L2Inner α α) + Real.sqrt (L2Inner β β) := rfl

/-- L2 norm homogeneity (derived from inner product linearity). -/
theorem L2NormForm_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    L2NormForm (r • α) = |r| * L2NormForm α := by
  unfold L2NormForm
  rw [L2Inner_smul_left, L2Inner_smul_right]
  -- sqrt(r * (r * x)) = sqrt(r² * x) = |r| * sqrt(x)
  have h1 : r * (r * L2Inner α α) = r ^ 2 * L2Inner α α := by ring
  rw [h1, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

end
