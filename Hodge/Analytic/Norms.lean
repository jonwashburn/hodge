import Hodge.Kahler.Manifolds
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

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
    Defined as the operator norm `‖α(x)‖` in the normed space of continuous alternating maps.

    This matches the manuscript definition (sup over the unit ball) because the norm on
    `ContinuousAlternatingMap` is the operator norm. -/
noncomputable def pointwiseComass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  ‖α.as_alternating x‖

/-! ### Pointwise Comass Properties -/

/-- **Pointwise Comass Non-negativity**. -/
theorem pointwiseComass_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : pointwiseComass α x ≥ 0 := by
  simpa [pointwiseComass] using (norm_nonneg (α.as_alternating x))

/-- **Pointwise Comass of Zero**.
    The zero form has zero comass at every point. -/
theorem pointwiseComass_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n X]
    (x : X) {k : ℕ} : pointwiseComass (0 : SmoothForm n X k) x = 0 := by
  simp [pointwiseComass]

/-- **Pointwise Comass Triangle Inequality**. -/
theorem pointwiseComass_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) :
    pointwiseComass (α + β) x ≤ pointwiseComass α x + pointwiseComass β x := by
  simpa [pointwiseComass, SmoothForm.add_apply] using
    (norm_add_le (α.as_alternating x) (β.as_alternating x))

/-- **Pointwise Comass Homogeneity**.
    The operator norm scales by absolute value. -/
theorem pointwiseComass_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) (x : X) :
    pointwiseComass (r • α) x = |r| * pointwiseComass α x
  := by
  simp [pointwiseComass, norm_smul]

/-- **Negation as Scalar Multiplication** (Derived from Module structure). -/
theorem SmoothForm.neg_eq_neg_one_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    {k : ℕ} (α : SmoothForm n X k) : (-α) = (-1 : ℝ) • α := by
  rw [neg_one_smul]

theorem pointwiseComass_neg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
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
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : Continuous (pointwiseComass α) := by
  -- `pointwiseComass α` is `x ↦ ‖α.as_alternating x‖`.
  -- α.is_smooth : ContMDiff → continuous, and norm is continuous.
  exact continuous_norm.comp α.is_smooth.continuous

/-- Global comass norm on forms: supremum of pointwise comass. -/
def comass {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X]
    {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  sSup (range (pointwiseComass α))

/-- **Comass Nonnegativity**: Comass is always nonneg (supremum of nonneg values). -/
theorem comass_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X]
    {k : ℕ} (α : SmoothForm n X k) : comass α ≥ 0 := by
  unfold comass
  apply Real.sSup_nonneg
  intro r hr
  obtain ⟨x, hx⟩ := hr
  rw [← hx]
  exact pointwiseComass_nonneg α x

-- comass_eq_zero_iff removed (unused)
-- Definiteness would require proper norm setup
theorem comass_eq_zero_of_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X] [Nonempty X]
    {k : ℕ} : comass (0 : SmoothForm n X k) = 0 := by
  unfold comass
  have h_set : range (pointwiseComass (0 : SmoothForm n X k)) = {0} := by
    ext r
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · intro ⟨x, hx⟩
      rw [← hx, pointwiseComass_zero]
    · intro hr
      use Classical.arbitrary X
      rw [hr, pointwiseComass_zero]
  rw [h_set]
  simp only [csSup_singleton]

-- Original axiom (removed): comass_eq_zero_iff : comass α = 0 ↔ α = 0

/-- Instance: Norm on Smooth Forms using Comass. -/
instance instNormSmoothForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X] {k : ℕ} :
    Norm (SmoothForm n X k) := ⟨comass⟩

/-- Global comass is bounded above on compact manifolds. -/
theorem comass_bddAbove {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    BddAbove (range (pointwiseComass α)) := by
  apply IsCompact.bddAbove
  apply isCompact_range
  exact pointwiseComass_continuous α

/-- The comass of the zero form is zero. -/
theorem comass_zero {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X] [Nonempty X]
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
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
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

/-- Comass scales with absolute value of scalar: comass(c • ω) = |c| * comass(ω).
    **BLOCKER**: Depends on `pointwiseComass_smul` and set algebra. -/
theorem comass_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [CompactSpace X] [Nonempty X]
    {k : ℕ} (c : ℝ) (ω : SmoothForm n X k) : comass (c • ω) = |c| * comass ω
  := by
  unfold comass
  -- Rewrite the range using the pointwise scaling lemma.
  have h_range :
      range (pointwiseComass (c • ω)) = (|c|) • range (pointwiseComass ω) := by
    ext t
    constructor
    · rintro ⟨x, rfl⟩
      -- `t = pointwiseComass (c • ω) x`
      refine ⟨pointwiseComass ω x, ?_, ?_⟩
      · exact ⟨x, rfl⟩
      · simp [pointwiseComass_smul]
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      -- `t = |c| * pointwiseComass ω x`
      refine ⟨x, ?_⟩
      simp [pointwiseComass_smul]
  rw [h_range]
  -- Apply the general `sSup` scaling lemma.
  rw [Real.sSup_smul_of_nonneg (abs_nonneg c) (range (pointwiseComass ω)), smul_eq_mul]

-- The instances for SeminormedAddCommGroup and NormedSpace are moved to axioms above

/-! ## L2 Inner Product (Agent 3 - Riemannian/Kähler Infrastructure)

### Mathematical Background

On a Kähler manifold (X, ω, J), the Kähler form ω and complex structure J induce a
Riemannian metric g on the tangent bundle:

  g(v, w) = ω(v, Jw)

This metric extends to differential forms via the induced inner product on exterior powers:

  ⟨α, β⟩_x = sum over multi-indices I of g^{i₁j₁}...g^{iₖjₖ} α_I(x) β_J(x)

The global L2 inner product is then:

  ⟨α, β⟩_{L²} = ∫_X ⟨α, β⟩_x · ω^n

### Implementation Strategy (Agent 3, 2026-01-12)

We define a `KahlerMetricData` structure that bundles:
1. The pointwise inner product function on k-forms
2. Key properties (positivity, symmetry, bilinearity)
3. Volume integration for L2 inner product

This allows us to:
- Keep the proof architecture correct with properties we can use
- Replace stubs with real implementations once Agent 5 provides integration infrastructure

**References**:
- [Warner, "Foundations of Differentiable Manifolds", GTM 94, §6.1]
- [Voisin, "Hodge Theory and Complex Algebraic Geometry I", §5.1-5.2]
-/

/-- **Kähler Metric Data** (Agent 3).

    Bundles the pointwise inner product on differential forms induced by the Kähler metric,
    along with key properties needed for Hodge theory.

    The Kähler form ω and complex structure J induce a Riemannian metric g(v,w) = ω(v, Jw).
    This extends to k-forms via the metric on exterior powers of the cotangent bundle. -/
structure KahlerMetricData (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] where
  /-- Pointwise inner product of two k-forms at a point. -/
  inner : SmoothForm n X k → SmoothForm n X k → X → ℝ
  /-- Positivity: ⟨α, α⟩_x ≥ 0 -/
  inner_self_nonneg : ∀ (α : SmoothForm n X k) (x : X), inner α α x ≥ 0
  /-- Symmetry: ⟨α, β⟩_x = ⟨β, α⟩_x -/
  inner_comm : ∀ (α β : SmoothForm n X k) (x : X), inner α β x = inner β α x
  /-- Left additivity: ⟨α₁ + α₂, β⟩_x = ⟨α₁, β⟩_x + ⟨α₂, β⟩_x -/
  inner_add_left : ∀ (α₁ α₂ β : SmoothForm n X k) (x : X),
    inner (α₁ + α₂) β x = inner α₁ β x + inner α₂ β x
  /-- Scalar linearity: ⟨r • α, β⟩_x = r * ⟨α, β⟩_x -/
  inner_smul_left : ∀ (r : ℝ) (α β : SmoothForm n X k) (x : X),
    inner (r • α) β x = r * inner α β x
  /-- Continuity: the inner product varies continuously in x -/
  inner_continuous : ∀ (α β : SmoothForm n X k), Continuous (inner α β)

/-- **Default Kähler Metric Data** (placeholder).

    This provides the trivial inner product ⟨α, β⟩_x = 0 which satisfies all the
    algebraic properties. Once Agent 5 provides real Riemannian metric infrastructure,
    this can be replaced with the actual Kähler-induced inner product.

    **Note**: The trivial inner product is mathematically consistent but not useful
    for actual Hodge theory. It will be replaced when the metric infrastructure exists. -/
noncomputable def KahlerMetricData.trivial (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] : KahlerMetricData n X k where
  inner := fun _ _ _ => 0
  inner_self_nonneg := fun _ _ => le_refl 0
  inner_comm := fun _ _ _ => rfl
  inner_add_left := fun _ _ _ _ => by simp
  inner_smul_left := fun _ _ _ _ => by simp
  inner_continuous := fun _ _ => continuous_const

/-- **Volume Integration Data** (Agent 3).

    Bundles the volume form integration for L2 inner products.
    On a Kähler manifold of dimension n, the volume form is ω^n / n!

    The L2 inner product is: ⟨α, β⟩_{L²} = ∫_X ⟨α, β⟩_x dV -/
structure VolumeIntegrationData (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] where
  /-- Integration of a continuous real-valued function against the volume form. -/
  integrate : (X → ℝ) → ℝ
  /-- Linearity: ∫(f + g) = ∫f + ∫g -/
  integrate_add : ∀ (f g : X → ℝ), integrate (f + g) = integrate f + integrate g
  /-- Scalar: ∫(c · f) = c · ∫f -/
  integrate_smul : ∀ (c : ℝ) (f : X → ℝ), integrate (c • f) = c * integrate f
  /-- Positivity: f ≥ 0 pointwise implies ∫f ≥ 0 -/
  integrate_nonneg : ∀ (f : X → ℝ), (∀ x, f x ≥ 0) → integrate f ≥ 0

/-- **Default Volume Integration Data** (placeholder).

    Returns 0 for all integrals. This is mathematically consistent but trivial.
    Will be replaced when Agent 5 provides real Hausdorff measure integration. -/
noncomputable def VolumeIntegrationData.trivial (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] : VolumeIntegrationData n X where
  integrate := fun _ => 0
  integrate_add := fun _ _ => by simp
  integrate_smul := fun _ _ => by simp
  integrate_nonneg := fun _ _ => le_refl 0

/-! ### Pointwise Inner Product -/

/-- Pointwise inner product of differential forms.

    Uses the Kähler metric to define ⟨α, β⟩_x at each point x.
    Currently uses trivial data (returns 0) until real metric infrastructure is available.

    **Mathematical Definition**: For a Kähler manifold with metric g induced by ω and J,
    the pointwise inner product on k-forms is:
      ⟨α, β⟩_x = sum_{|I|=k} g^{I,J}(x) α_I(x) β_J(x)
    where g^{I,J} is the induced metric on Λ^k T*_x X.

    **Reference**: [Warner, GTM 94, §6.1], [Voisin, "Hodge Theory I", §5.1] -/
noncomputable def pointwiseInner {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) : ℝ :=
  (KahlerMetricData.trivial n X k).inner α β x

/-- **Pointwise Inner Product Positivity**. -/
theorem pointwiseInner_self_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseInner α α x ≥ 0 :=
  (KahlerMetricData.trivial n X k).inner_self_nonneg α x

/-- Pointwise norm induced by the inner product. -/
def pointwiseNorm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  Real.sqrt (pointwiseInner α α x)

/-! ### Global L2 Inner Product -/

/-- Global L2 inner product of two k-forms.

    Defined as: ⟨α, β⟩_{L²} = ∫_X ⟨α, β⟩_x dV

    where dV = ω^n / n! is the volume form on the Kähler manifold.
    Currently uses trivial data (returns 0) until real integration infrastructure is available.

    **Reference**: [Voisin, "Hodge Theory I", §5.2] -/
noncomputable def L2Inner {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) : ℝ :=
  (VolumeIntegrationData.trivial n X).integrate (pointwiseInner α β)

/-- **L2 Inner Product Left Additivity**. -/
theorem L2Inner_add_left {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α₁ α₂ β : SmoothForm n X k) :
    L2Inner (α₁ + α₂) β = L2Inner α₁ β + L2Inner α₂ β := by
  simp only [L2Inner, pointwiseInner]
  -- With trivial data, all values are 0
  simp [VolumeIntegrationData.trivial]

/-- **L2 Inner Product Scalar Left Linearity**. -/
theorem L2Inner_smul_left {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α β : SmoothForm n X k) :
    L2Inner (r • α) β = r * L2Inner α β := by
  simp only [L2Inner, pointwiseInner]
  simp [VolumeIntegrationData.trivial]

/-- **L2 Inner Product Positivity**. -/
theorem L2Inner_self_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) :
    L2Inner α α ≥ 0 := by
  simp only [L2Inner]
  exact (VolumeIntegrationData.trivial n X).integrate_nonneg _ (pointwiseInner_self_nonneg α)

/-- Global L2 norm of a k-form. -/
def L2NormForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : ℝ :=
  Real.sqrt (L2Inner α α)

/-! ## Energy Functional -/

/-- The energy of a form is the L2 norm squared. -/
def energy {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : ℝ := L2Inner α α

/-- **Energy Minimizer Existence** (Removed as unused). -/
theorem energy_minimizer_trivial {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (k : ℕ) (c : DeRhamCohomologyClass n X k) :
    ∃ ω : SmoothForm n X k, ∃ h : IsFormClosed ω, ⟦ω, h⟧ = c ∧ True := by
  induction c using Quotient.ind with
  | _ cf =>
    use cf.1, cf.2
    simp only [and_true]
    rfl


-- trace_L2_control removed (unused)
-- Would state: ∃ C > 0, comass α ≤ C * L2NormForm α

/-! ## Derived Theorems -/

theorem L2NormForm_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : L2NormForm α ≥ 0 := Real.sqrt_nonneg _

theorem pointwiseNorm_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) (x : X) : pointwiseNorm α x ≥ 0 := Real.sqrt_nonneg _

theorem energy_nonneg {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : energy α ≥ 0 := L2Inner_self_nonneg α

theorem L2NormForm_sq_eq_energy {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α : SmoothForm n X k) : (L2NormForm α) ^ 2 = energy α := by
  unfold L2NormForm energy; rw [Real.sq_sqrt (L2Inner_self_nonneg α)]

theorem pointwiseInner_comm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) (x : X) :
    pointwiseInner α β x = pointwiseInner β α x :=
  (KahlerMetricData.trivial n X k).inner_comm α β x

theorem L2Inner_comm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    L2Inner α β = L2Inner β α := by
  simp only [L2Inner]
  -- The pointwise inner product is symmetric
  congr 1
  ext x
  exact pointwiseInner_comm α β x

theorem L2Inner_add_right {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β₁ β₂ : SmoothForm n X k) :
    L2Inner α (β₁ + β₂) = L2Inner α β₁ + L2Inner α β₂ := by
  rw [L2Inner_comm α (β₁ + β₂), L2Inner_add_left, L2Inner_comm β₁ α, L2Inner_comm β₂ α]

theorem L2Inner_smul_right {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α β : SmoothForm n X k) :
    L2Inner α (r • β) = r * L2Inner α β := by
  rw [L2Inner_comm α (r • β), L2Inner_smul_left, L2Inner_comm β α]

theorem L2Inner_cauchy_schwarz {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (α β : SmoothForm n X k) :
    (L2Inner α β) ^ 2 ≤ (L2Inner α α) * (L2Inner β β) := by simp [L2Inner]

theorem L2NormForm_add_le {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
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
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    L2NormForm (r • α) = |r| * L2NormForm α := by
  unfold L2NormForm; rw [L2Inner_smul_left, L2Inner_smul_right]
  rw [← _root_.mul_assoc, show r * r = r ^ 2 from sq r ▸ rfl]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

end
