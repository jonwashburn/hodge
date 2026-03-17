import Hodge.Analytic.Forms
import Hodge.Analytic.Norms
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.Support
import Mathlib.Algebra.Group.Defs

/-!
# Currents on Kähler Manifolds

This file defines currents (distributional differential forms) on compact Kähler manifolds.
A current is defined as a continuous linear functional on the space of smooth forms.
-/

noncomputable section

open Classical Hodge MeasureTheory

set_option autoImplicit false

/-!
### Measurable structure on the model tangent space

We frequently need measurability of maps into the model fiber `TangentModel n = ℂⁿ`.
Mathlib does not provide a default `MeasurableSpace` instance for every topological space,
so we declare the Borel measurable space explicitly for `TangentModel`.
-/

instance (n : ℕ) : MeasurableSpace (TangentModel n) := borel (TangentModel n)
instance (n : ℕ) : BorelSpace (TangentModel n) := ⟨rfl⟩

-- Likewise, we equip the space of continuous alternating maps with its Borel measurable space.
instance (n k : ℕ) : MeasurableSpace (FiberAlt n k) := borel (FiberAlt n k)
instance (n k : ℕ) : BorelSpace (FiberAlt n k) := ⟨rfl⟩

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]

/-- A current of dimension k is a **continuous ℝ-linear functional** on smooth k-forms.

This is the functional-analytic reformulation of the earlier data-carrying structure:
`toFun` is now a `ContinuousLinearMap`, so boundedness with respect to the comass seminorm
is derived (and no longer stored as a per-current field).

We *still* record a separate `boundary_bound` hypothesis (normality-style): comass is a
`C^0`-type seminorm, so continuity does **not** automatically control `ω ↦ T(dω)`. -/
structure Current (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] where
  /-- The underlying continuous ℝ-linear functional on k-forms. -/
  toFun : SmoothForm n X k →L[ℝ] ℝ
  /-- **Boundary boundedness** (normality-style hypothesis): for `k = k' + 1`, the functional
      `ω ↦ T(dω)` is bounded with respect to the comass seminorm on `k'`-forms.

  This is exactly what is needed to define the boundary current `∂T` as a `Current`.
  For `k = 0` there is no boundary, so we record `True`. -/
  boundary_bound :
    match k with
    | 0 => True
    | k' + 1 => ∃ M : ℝ, ∀ ω : SmoothForm n X k', |toFun (smoothExtDeriv ω)| ≤ M * ‖ω‖

namespace Current

variable {k : ℕ}

/-! ## Support of a Current

The **support** of a current T is the smallest closed set Z such that T(ω) = 0
for all smooth forms ω whose support is disjoint from Z. This is a fundamental
concept in GMT that characterizes "where" a current lives.

For our purposes, we define support operationally as the closure of the set
of points where the current "acts" non-trivially.

Reference: [Federer, "Geometric Measure Theory", 1969, §4.1.7].
-/

/-- **Support of a Current** (placeholder definition).

    The support of a current T is the smallest closed set Z ⊆ X such that
    T(ω) = 0 whenever supp(ω) ∩ Z = ∅.

    **Implementation Note**: We use the standard distribution-theoretic definition:
    `support T` is the complement of the largest open set on which `T` vanishes on all
    compactly supported smooth forms.

    Reference: [Federer, "Geometric Measure Theory", 1969, §4.1.7]. -/
def support {n k : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (T : Current n X k) : Set X :=
  -- Union of all open sets on which the current vanishes on compactly supported forms,
  -- then take the complement.
  (⋃ (U : Set X) (_hU : IsOpen U)
      (_hzero :
        ∀ ω : SmoothForm n X k,
          HasCompactSupport ω.as_alternating →
            tsupport ω.as_alternating ⊆ U → T.toFun ω = 0),
      U)ᶜ

/-- The support of a current is closed (placeholder). -/
theorem support_isClosed {n k : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (T : Current n X k) : IsClosed (support T) := by
  classical
  -- `support T` is the complement of a union of open sets, hence closed.
  have hopen :
      IsOpen
        (⋃ (U : Set X) (_hU : IsOpen U)
            (_hzero :
              ∀ ω : SmoothForm n X k,
                HasCompactSupport ω.as_alternating →
                  tsupport ω.as_alternating ⊆ U → T.toFun ω = 0),
            U) := by
    refine isOpen_iUnion ?_
    intro U
    refine isOpen_iUnion ?_
    intro hU
    refine isOpen_iUnion ?_
    intro _hzero
    exact hU
  simpa [support] using hopen.isClosed_compl

/-- Extensionality for currents: two currents are equal iff they agree on all forms. -/
@[ext]
theorem ext' {n k : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    {S T : Current n X k} (h : ∀ ω, S.toFun ω = T.toFun ω) : S = T := by
  cases S with
  | mk Sfun Sbd =>
    cases T with
    | mk Tfun Tbd =>
      have hfun : Sfun = Tfun := by
        ext ω
        exact h ω
      subst hfun
      have hbd : Sbd = Tbd := by
        -- proof-irrelevance for Prop fields
        apply Subsingleton.elim
      subst hbd
      rfl

/-- Linearity properties derive from the `is_linear` field. -/
theorem map_add {n k : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (T : Current n X k) (ω₁ ω₂ : SmoothForm n X k) :
    T.toFun (ω₁ + ω₂) = T.toFun ω₁ + T.toFun ω₂ := by
  simpa using T.toFun.map_add ω₁ ω₂

/-- Currents map zero to zero. Follows from map_add with ω₁=ω₂=0. -/
theorem map_zero' {n k : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (T : Current n X k) : T.toFun 0 = 0 := by
  simpa using T.toFun.map_zero

/-- Linearity: scalar multiplication. Derives from the is_linear field with ω₂ = 0. -/
theorem map_smul {n k : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (T : Current n X k) (r : ℝ) (ω : SmoothForm n X k) : T.toFun (r • ω) = r * T.toFun ω := by
  -- `toFun` is an ℝ-linear map, so scalar multiplication is respected.
  simpa [smul_eq_mul] using (T.toFun.map_smul r ω)

/-- The zero current evaluates to zero on all forms. -/
def zero (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] : Current n X k where
  toFun := 0
  boundary_bound := by
    cases k with
    | zero => trivial
    | succ k' =>
      refine ⟨0, ?_⟩
      intro ω
      simp

instance instInhabited : Inhabited (Current n X k) := ⟨zero n X k⟩
instance instZero : Zero (Current n X k) := ⟨zero n X k⟩

@[simp] theorem support_zero {n k : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X] :
    support (n := n) (X := X) (k := k) (Zero.zero : Current n X k) = (∅ : Set X) := by
  classical
  let T0 : Current n X k := (Zero.zero : Current n X k)
  have hUnion :
      (⋃ (U : Set X) (_hU : IsOpen U)
          (_hzero :
            ∀ ω : SmoothForm n X k,
              HasCompactSupport ω.as_alternating →
                tsupport ω.as_alternating ⊆ U → T0.toFun ω = 0),
          U) = (Set.univ : Set X) := by
    ext x
    constructor
    · intro _; simp
    · intro _hx
      refine Set.mem_iUnion_of_mem (Set.univ : Set X) ?_
      refine Set.mem_iUnion_of_mem isOpen_univ ?_
      have hzero :
          ∀ ω : SmoothForm n X k,
            HasCompactSupport ω.as_alternating →
              tsupport ω.as_alternating ⊆ (Set.univ : Set X) →
                T0.toFun ω = 0 := by
        intro ω _ _
        rfl
      refine Set.mem_iUnion_of_mem hzero ?_
      simp
  ext x
  constructor
  · intro hx
    have hx' : x ∈ (⋃ (U : Set X) (_hU : IsOpen U)
        (_hzero :
          ∀ ω : SmoothForm n X k,
            HasCompactSupport ω.as_alternating →
              tsupport ω.as_alternating ⊆ U → T0.toFun ω = 0),
        U)ᶜ := by
      simpa [support] using hx
    have hx'' : x ∉ (Set.univ : Set X) := by
      simpa [hUnion] using hx'
    simpa using hx''
  · intro hx
    simpa using hx

/-- Addition of currents: (T₁ + T₂)(ω) = T₁(ω) + T₂(ω). -/
def add_curr (T₁ T₂ : Current n X k) : Current n X k where
  toFun := T₁.toFun + T₂.toFun
  boundary_bound := by
    cases k with
    | zero => trivial
    | succ k' =>
      -- Use the boundary bounds of each summand.
      obtain ⟨M₁, hM₁⟩ := T₁.boundary_bound
      obtain ⟨M₂, hM₂⟩ := T₂.boundary_bound
      refine ⟨M₁ + M₂, ?_⟩
      intro ω
      have h1 := hM₁ ω
      have h2 := hM₂ ω
      -- (T₁+T₂)(dω) = T₁(dω) + T₂(dω)
      calc
        |(T₁.toFun + T₂.toFun) (smoothExtDeriv ω)|
            ≤ |T₁.toFun (smoothExtDeriv ω)| + |T₂.toFun (smoothExtDeriv ω)| := abs_add_le _ _
        _ ≤ M₁ * ‖ω‖ + M₂ * ‖ω‖ := add_le_add h1 h2
        _ = (M₁ + M₂) * ‖ω‖ := by ring

instance : Add (Current n X k) := ⟨add_curr⟩

/-- Negation of currents: (-T)(ω) = -T(ω). -/
def neg_curr (T : Current n X k) : Current n X k where
  toFun := -T.toFun
  boundary_bound := by
    cases k with
    | zero => trivial
    | succ k' =>
      obtain ⟨M, hM⟩ := T.boundary_bound
      refine ⟨M, ?_⟩
      intro ω
      simpa using (hM ω)

instance : Neg (Current n X k) := ⟨neg_curr⟩

/-- Negation of zero is zero. -/
theorem neg_zero_current : -(0 : Current n X k) = 0 := by
  ext ω
  -- (-0).toFun ω = -(0.toFun ω) = -0 = 0 = 0.toFun ω
  show -(0 : Current n X k).toFun ω = (0 : Current n X k).toFun ω
  -- 0.toFun ω = 0 by definition
  have h : (0 : Current n X k).toFun ω = 0 := rfl
  rw [h]
  -- -0 = 0
  ring

instance : Sub (Current n X k) := ⟨fun T₁ T₂ => T₁ + -T₂⟩

/-! ### Additive commutative group structure

We will need permutation-invariant finite sums of currents (TeX “matching over permutations”),
so we register `AddCommGroup` on `Current n X k`, with `nsmul`/`zsmul`/`sub` set to the
standard recursion-based definitions.
-/

instance instAddCommGroup : AddCommGroup (Current n X k) where
  add := (· + ·)
  add_assoc := by
    intro A B C
    ext ω
    change (A.toFun ω + B.toFun ω) + C.toFun ω = A.toFun ω + (B.toFun ω + C.toFun ω)
    exact add_assoc _ _ _
  zero := 0
  zero_add := by
    intro A
    ext ω
    change (0 : Current n X k).toFun ω + A.toFun ω = A.toFun ω
    have h0 : (0 : Current n X k).toFun ω = 0 := rfl
    simp [h0]
  add_zero := by
    intro A
    ext ω
    change A.toFun ω + (0 : Current n X k).toFun ω = A.toFun ω
    have h0 : (0 : Current n X k).toFun ω = 0 := rfl
    simp [h0]
  nsmul := nsmulRec
  neg := Neg.neg
  sub := fun a b => a + -b
  sub_eq_add_neg := by
    intro a b
    rfl
  zsmul := zsmulRec (nsmul := nsmulRec)
  neg_add_cancel := by
    intro A
    ext ω
    -- rewrite everything down to a ring identity in `ℝ`.
    have hneg : (-A).toFun ω = -(A.toFun ω) := rfl
    have h0 : (0 : Current n X k).toFun ω = 0 := rfl
    -- goal: (-A)(ω) + A(ω) = 0(ω)
    change (-A).toFun ω + A.toFun ω = (0 : Current n X k).toFun ω
    rw [hneg, h0]
    ring
  add_comm := by
    intro A B
    ext ω
    change A.toFun ω + B.toFun ω = B.toFun ω + A.toFun ω
    exact add_comm _ _

/-- Scalar multiplication of currents: (r • T)(ω) = r * T(ω). -/
def smul_curr (r : ℝ) (T : Current n X k) : Current n X k where
  toFun := r • T.toFun
  boundary_bound := by
    cases k with
    | zero => trivial
    | succ k' =>
      obtain ⟨M, hM⟩ := T.boundary_bound
      refine ⟨|r| * M, ?_⟩
      intro ω
      have h := hM ω
      calc
        |(r • T.toFun) (smoothExtDeriv ω)| = |r| * |T.toFun (smoothExtDeriv ω)| := by
          simp [Real.norm_eq_abs, abs_mul, mul_assoc]
        _ ≤ |r| * (M * ‖ω‖) := mul_le_mul_of_nonneg_left h (abs_nonneg r)
        _ = (|r| * M) * ‖ω‖ := by ring

instance : HSMul ℝ (Current n X k) (Current n X k) := ⟨smul_curr⟩
instance : HSMul ℤ (Current n X k) (Current n X k) := ⟨fun z T => (z : ℝ) • T⟩

theorem support_add_subset {n k : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (T₁ T₂ : Current n X k) :
    support (n := n) (X := X) (k := k) (T₁ + T₂) ⊆ support T₁ ∪ support T₂ := by
  classical
  intro x hx
  by_contra h
  have hx' : ¬ (x ∈ support T₁ ∨ x ∈ support T₂) := by
    simpa using h
  have hx1 : x ∉ support T₁ := (not_or.mp hx').1
  have hx2 : x ∉ support T₂ := (not_or.mp hx').2
  rcases (by
    simpa [support] using hx1) with ⟨U₁, hU₁, hzero₁, hxU₁⟩
  rcases (by
    simpa [support] using hx2) with ⟨U₂, hU₂, hzero₂, hxU₂⟩
  let U : Set X := U₁ ∩ U₂
  have hU : IsOpen U := hU₁.inter hU₂
  have hxU : x ∈ U := ⟨hxU₁, hxU₂⟩
  have hzero :
      ∀ ω : SmoothForm n X k,
        HasCompactSupport ω.as_alternating →
          tsupport ω.as_alternating ⊆ U → (T₁ + T₂).toFun ω = 0 := by
    intro ω hcomp hsub
    have hsub₁ : tsupport ω.as_alternating ⊆ U₁ := by
      intro y hy
      exact (hsub hy).1
    have hsub₂ : tsupport ω.as_alternating ⊆ U₂ := by
      intro y hy
      exact (hsub hy).2
    have h₁ := hzero₁ ω hcomp hsub₁
    have h₂ := hzero₂ ω hcomp hsub₂
    change (T₁.toFun + T₂.toFun) ω = 0
    simp [h₁, h₂]
  have hxUnion :
      x ∈ ⋃ (U : Set X) (_hU : IsOpen U)
        (_hzero :
          ∀ ω : SmoothForm n X k,
            HasCompactSupport ω.as_alternating →
              tsupport ω.as_alternating ⊆ U → (T₁ + T₂).toFun ω = 0),
        U := by
    refine Set.mem_iUnion_of_mem U ?_
    refine Set.mem_iUnion_of_mem hU ?_
    refine Set.mem_iUnion_of_mem hzero ?_
    exact hxU
  have hxNot : x ∉ support (n := n) (X := X) (k := k) (T₁ + T₂) := by
    intro hxSupp
    exact hxSupp hxUnion
  exact hxNot hx

theorem support_smul_subset {n k : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (r : ℝ) (T : Current n X k) :
    support (n := n) (X := X) (k := k) (r • T) ⊆ support T := by
  classical
  intro x hx
  by_contra h
  have hxT : x ∉ support T := by simpa using h
  rcases (by
    simpa [support] using hxT) with ⟨U, hU, hzero, hxU⟩
  have hzero' :
      ∀ ω : SmoothForm n X k,
        HasCompactSupport ω.as_alternating →
          tsupport ω.as_alternating ⊆ U → (r • T).toFun ω = 0 := by
    intro ω hcomp hsub
    have hT0 := hzero ω hcomp hsub
    change (r • T.toFun) ω = 0
    simp [hT0]
  have hxUnion :
      x ∈ ⋃ (U : Set X) (_hU : IsOpen U)
        (_hzero :
          ∀ ω : SmoothForm n X k,
            HasCompactSupport ω.as_alternating →
              tsupport ω.as_alternating ⊆ U → (r • T).toFun ω = 0),
        U := by
    refine Set.mem_iUnion_of_mem U ?_
    refine Set.mem_iUnion_of_mem hU ?_
    refine Set.mem_iUnion_of_mem hzero' ?_
    exact hxU
  have hxNot : x ∉ support (n := n) (X := X) (k := k) (r • T) := by
    intro hxSupp
    exact hxSupp hxUnion
  exact hxNot hx

theorem support_smul_eq {n k : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (r : ℝ) (hr : r ≠ 0) (T : Current n X k) :
    support (n := n) (X := X) (k := k) (r • T) = support T := by
  apply Set.Subset.antisymm
  · exact support_smul_subset (n := n) (X := X) (k := k) r T
  · have hsubset :
      support (n := n) (X := X) (k := k) ((r⁻¹) • (r • T)) ⊆
        support (n := n) (X := X) (k := k) (r • T) :=
      support_smul_subset (n := n) (X := X) (k := k) (r := r⁻¹) (T := r • T)
    have hrep : (r⁻¹) • (r • T) = T := by
      ext ω
      simpa [smul_curr, smul_eq_mul, mul_assoc] using
        (inv_mul_cancel_left₀ hr (T.toFun ω))
    simpa [hrep] using hsubset

theorem support_neg_subset {n k : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (T : Current n X k) :
    support (n := n) (X := X) (k := k) (-T) ⊆ support T := by
  classical
  intro x hx
  by_contra h
  have hxT : x ∉ support T := by simpa using h
  rcases (by
    simpa [support] using hxT) with ⟨U, hU, hzero, hxU⟩
  have hzero' :
      ∀ ω : SmoothForm n X k,
        HasCompactSupport ω.as_alternating →
          tsupport ω.as_alternating ⊆ U → (-T).toFun ω = 0 := by
    intro ω hcomp hsub
    have hT0 := hzero ω hcomp hsub
    change (-T.toFun) ω = 0
    simp [hT0]
  have hxUnion :
      x ∈ ⋃ (U : Set X) (_hU : IsOpen U)
        (_hzero :
          ∀ ω : SmoothForm n X k,
            HasCompactSupport ω.as_alternating →
              tsupport ω.as_alternating ⊆ U → (-T).toFun ω = 0),
        U := by
    refine Set.mem_iUnion_of_mem U ?_
    refine Set.mem_iUnion_of_mem hU ?_
    refine Set.mem_iUnion_of_mem hzero' ?_
    exact hxU
  have hxNot : x ∉ support (n := n) (X := X) (k := k) (-T) := by
    intro hxSupp
    exact hxSupp hxUnion
  exact hxNot hx

theorem support_neg_eq {n k : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (T : Current n X k) :
    support (n := n) (X := X) (k := k) (-T) = support T := by
  apply Set.Subset.antisymm
  · exact support_neg_subset (n := n) (X := X) (k := k) T
  · have hsubset :
      support (n := n) (X := X) (k := k) (-(-T)) ⊆
        support (n := n) (X := X) (k := k) (-T) :=
      support_neg_subset (n := n) (X := X) (k := k) (-T)
    simpa using hsubset

theorem support_sub_subset {n k : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (T₁ T₂ : Current n X k) :
    support (n := n) (X := X) (k := k) (T₁ - T₂) ⊆ support T₁ ∪ support T₂ := by
  have hadd :
      support (n := n) (X := X) (k := k) (T₁ + (-T₂)) ⊆ support T₁ ∪ support (-T₂) := by
    simpa using (support_add_subset (n := n) (X := X) (k := k) T₁ (-T₂))
  have hneg : support (n := n) (X := X) (k := k) (-T₂) ⊆ support T₂ :=
    support_neg_subset (n := n) (X := X) (k := k) T₂
  have hsubset : support T₁ ∪ support (-T₂) ⊆ support T₁ ∪ support T₂ := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hneg hx)
  intro x hx
  have hx' : x ∈ support T₁ ∪ support (-T₂) := by
    have hx'' : x ∈ support (n := n) (X := X) (k := k) (T₁ + (-T₂)) := by
      simpa [sub_eq_add_neg] using hx
    exact hadd hx''
  exact hsubset hx'

/-- Zero current evaluates to zero. -/
theorem zero_toFun (ω : SmoothForm n X k) : (0 : Current n X k).toFun ω = 0 := rfl

/-- **Current Boundedness**: Every current is bounded relative to the comass.

    **Note**: The proof requires the metric topology on `SmoothForm` to match
    the axiomatized topology `SmoothForm.instTopologicalSpace`. This is an
    infrastructure limitation. The mathematical content is standard:
    continuous linear maps between normed spaces are bounded.

    **Proof**: A continuous linear map between seminormed groups is bounded. -/
theorem is_bounded (T : Current n X k) : ∃ M : ℝ, ∀ ω : SmoothForm n X k, |T.toFun ω| ≤ M * ‖ω‖ := by
  refine ⟨‖T.toFun‖, ?_⟩
  intro ω
  -- `‖T ω‖ ≤ ‖T‖ * ‖ω‖` for continuous linear maps, and `‖·‖` on ℝ is `|·|`.
  simpa [Real.norm_eq_abs] using (T.toFun.le_opNorm ω)


/-- **Mass of a current** (Federer, 1969).
    The mass is the dual norm to the comass norm on forms:
    M(T) = sup { |T(ω)| : comass(ω) ≤ 1 } -/
def mass (T : Current n X k) : ℝ :=
  sSup { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |T.toFun ω| }

/-- The mass set is nonempty. -/
theorem mass_set_nonempty (T : Current n X k) :
    { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |T.toFun ω| }.Nonempty := by
  use |T.toFun 0|
  refine ⟨0, ?_, rfl⟩
  -- comass 0 = 0 ≤ 1
  rw [comass_eq_zero_of_zero]
  linarith

/-- The mass set is bounded above. -/
theorem mass_set_bddAbove (T : Current n X k) :
    BddAbove { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |T.toFun ω| } := by
  obtain ⟨M, hM⟩ := T.is_bounded
  use max M 0
  intro r ⟨ω, hω_comass, hr⟩
  rw [hr]
  have h_bound := hM ω
  have h_comass_nonneg : comass ω ≥ 0 := comass_nonneg ω
  by_cases hM_nonneg : M ≥ 0
  · calc |T.toFun ω| ≤ M * ‖ω‖ := h_bound
      _ = M * comass ω := rfl
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left hω_comass hM_nonneg
      _ = M := mul_one M
      _ ≤ max M 0 := le_max_left M 0
  · push_neg at hM_nonneg
    have h1 : M * comass ω ≤ 0 := by nlinarith
    have h2 : |T.toFun ω| ≤ 0 := le_trans h_bound h1
    have h3 : |T.toFun ω| ≥ 0 := abs_nonneg _
    have h4 : |T.toFun ω| = 0 := le_antisymm h2 h3
    rw [h4]
    exact le_max_right M 0

/-- **Mass is non-negative**. -/
theorem mass_nonneg (T : Current n X k) : mass T ≥ 0 := by
  unfold mass; apply Real.sSup_nonneg
  intro r ⟨ω, _, hr⟩; rw [hr]; exact abs_nonneg _

/-- **Mass of zero current is zero**. -/
theorem mass_zero : mass (0 : Current n X k) = 0 := by
  unfold mass
  have h_set : { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |(0 : Current n X k).toFun ω| } = {0} := by
    ext r; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro ⟨ω, _, hr⟩; rw [hr, zero_toFun, abs_zero]
    · intro hr; use 0; simp [comass_zero, zero_toFun, hr]
  rw [h_set]; exact csSup_singleton 0

/-- **Mass is symmetric under negation**. -/
theorem mass_neg (T : Current n X k) : mass (-T) = mass T := by
  unfold mass
  have h_eq : ∀ ω, |(-T).toFun ω| = |T.toFun ω| := fun ω => by
    show |(-T.toFun ω)| = |T.toFun ω|
    exact abs_neg _
  simp_rw [h_eq]

/-- Mass satisfies the triangle inequality. -/
theorem mass_add_le (S T : Current n X k) : mass (S + T) ≤ mass S + mass T := by
  unfold mass
  -- (S + T).toFun ω = S.toFun ω + T.toFun ω
  have h_add : ∀ ω, (S + T).toFun ω = S.toFun ω + T.toFun ω := fun ω => by
    show (add_curr S T).toFun ω = S.toFun ω + T.toFun ω
    rfl
  -- For each ω: |(S + T)(ω)| ≤ |S(ω)| + |T(ω)| ≤ mass S + mass T
  apply csSup_le (mass_set_nonempty (S + T))
  intro r ⟨ω, hω_comass, hr⟩
  rw [hr, h_add]
  calc |S.toFun ω + T.toFun ω|
      ≤ |S.toFun ω| + |T.toFun ω| := abs_add_le _ _
    _ ≤ sSup {r | ∃ ω, comass ω ≤ 1 ∧ r = |S.toFun ω|} +
        sSup {r | ∃ ω, comass ω ≤ 1 ∧ r = |T.toFun ω|} := by
        apply add_le_add
        · apply le_csSup (mass_set_bddAbove S)
          exact ⟨ω, hω_comass, rfl⟩
        · apply le_csSup (mass_set_bddAbove T)
          exact ⟨ω, hω_comass, rfl⟩

/-- Mass scales with absolute value of scalar. -/
theorem mass_smul (r : ℝ) (T : Current n X k) : mass (r • T) = |r| * mass T := by
  unfold mass
  -- (r • T).toFun ω = r * T.toFun ω
  have h_smul : ∀ ω, (r • T).toFun ω = r * T.toFun ω := fun ω => rfl
  -- |r * x| = |r| * |x|
  have h_abs : ∀ ω, |(r • T).toFun ω| = |r| * |T.toFun ω| := fun ω => by
    rw [h_smul, abs_mul]
  simp_rw [h_abs]
  by_cases hr : r = 0
  · -- r = 0 case
    simp only [hr, abs_zero, MulZeroClass.zero_mul]
    -- Goal: sSup {r | ∃ ω, comass ω ≤ 1 ∧ r = 0} = 0
    have h_set : { x : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ x = 0 } = {0} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro ⟨_, _, hx⟩; exact hx
      · intro hx; subst hx; use 0; simp [comass_zero]
    rw [h_set, csSup_singleton]
  · -- r ≠ 0 case: |r| > 0
    have hr_pos : |r| > 0 := abs_pos.mpr hr
    -- The set { |r| * |T ω| : comass ω ≤ 1 } = (|r| * ·) '' { |T ω| : comass ω ≤ 1 }
    have h_image : { x : ℝ | ∃ ω, comass ω ≤ 1 ∧ x = |r| * |T.toFun ω| } =
        (fun x => |r| * x) '' { x : ℝ | ∃ ω, comass ω ≤ 1 ∧ x = |T.toFun ω| } := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro ⟨ω, hω, hx⟩; use |T.toFun ω|; exact ⟨⟨ω, hω, rfl⟩, hx.symm⟩
      · intro ⟨y, ⟨ω, hω, hy⟩, hxy⟩; use ω, hω; rw [← hxy, ← hy]
    rw [h_image]
    -- sSup (c * · '' S) = c * sSup S for c ≥ 0, S nonempty and bounded
    have h_nonempty := mass_set_nonempty T
    have h_bdd := mass_set_bddAbove T
    -- Use Monotone.map_csSup_of_continuousAt
    have h_mono : Monotone (fun x => |r| * x) := fun _ _ hab => mul_le_mul_of_nonneg_left hab (le_of_lt hr_pos)
    have h_cont : Continuous (fun x => |r| * x) := continuous_const.mul continuous_id
    rw [h_mono.map_csSup_of_continuousAt h_cont.continuousAt h_nonempty h_bdd]

/-- Extensionality for currents. -/
@[ext]
theorem ext {S T : Current n X k} (h : ∀ ω, S.toFun ω = T.toFun ω) : S = T := by
  cases S with
  | mk Sfun Sbd =>
    cases T with
    | mk Tfun Tbd =>
      have hfun : Sfun = Tfun := by
        ext ω
        exact h ω
      subst hfun
      have hbd : Sbd = Tbd := by
        apply Subsingleton.elim
      subst hbd
      rfl

theorem zero_add (T : Current n X k) : 0 + T = T := by
  ext ω
  show (0 : Current n X k).toFun ω + T.toFun ω = T.toFun ω
  rw [zero_toFun]; ring

theorem add_zero (T : Current n X k) : T + 0 = T := by
  ext ω
  show T.toFun ω + (0 : Current n X k).toFun ω = T.toFun ω
  rw [zero_toFun]; ring

theorem zero_sub (T : Current n X k) : 0 - T = -T := by
  ext ω
  show (0 : Current n X k).toFun ω + (-(T : Current n X k).toFun ω) = -T.toFun ω
  rw [zero_toFun]; ring

/-- **Boundary Operator Preserves Boundedness** (Infrastructure Axiom).

For any current T, the boundary functional ω ↦ T(dω) is bounded with respect to
the comass norm.

## Axiomatization Justification

This is axiomatized because it captures a fundamental property of currents in geometric
measure theory that cannot be derived from simpler principles in our current setup.

The previous approach attempted to prove this via a bound on the exterior derivative d,
but that approach was mathematically incorrect: d is NOT a bounded operator from C^0 to C^0
(the comass norm is a C^0 norm, and d involves differentiation).

## Mathematical Validity

This axiom IS valid for the currents used in the Hodge conjecture proof:

1. **Integration currents [Z]**: For a rectifiable set Z, by Stokes' theorem:
   `[Z](dω) = ∫_Z dω = ∫_∂Z ω`, so `|[Z](dω)| ≤ mass(∂Z) · comass(ω)`.

2. **Limits of integral currents**: Mass bounds are preserved under flat norm limits
   by the Federer-Fleming compactness theorem.

3. **Finite combinations**: Sums and scalar multiples of bounded currents remain bounded.

## Role in Proof

This axiom is used to show that `Current.boundary` returns a well-defined `Current`.
It is on the proof track but represents true mathematical content about the currents
we work with.

## References

- [Federer, "Geometric Measure Theory", 1969, Ch. 4]
- [Federer-Fleming, "Normal and integral currents", Ann. Math. 1960]
-/
def boundary (T : Current n X (k + 1)) : Current n X k where
  -- We build a continuous linear functional using the (axiomatized) boundary bound on `T`.
  -- NOTE: `smoothExtDeriv` is not continuous w.r.t. the comass seminorm, so we cannot use
  -- `T.toFun.comp`. Instead, we use `LinearMap.mkContinuousOfExistsBound`.
  toFun :=
    let f : SmoothForm n X k →ₗ[ℝ] ℝ :=
      { toFun := fun ω => T.toFun (smoothExtDeriv ω)
        map_add' := fun ω₁ ω₂ => by
          -- T(d(ω₁+ω₂)) = T(dω₁ + dω₂)
          simp [smoothExtDeriv_add]
        map_smul' := fun r ω => by
          -- T(d(r•ω)) = r * T(dω)
          simp [smoothExtDeriv_smul_real, map_smul] }
    have hbound : ∃ M : ℝ, ∀ ω : SmoothForm n X k, ‖f ω‖ ≤ M * ‖ω‖ := by
    -- This is exactly the `boundary_bound` field of `T` (since `k+1` is a successor).
      obtain ⟨M, hM⟩ := (T.boundary_bound : ∃ M : ℝ, ∀ ω : SmoothForm n X k, |T.toFun (smoothExtDeriv ω)| ≤ M * ‖ω‖)
      refine ⟨M, ?_⟩
      intro ω
      simpa [f, Real.norm_eq_abs] using (hM ω)
    f.mkContinuousOfExistsBound hbound
  boundary_bound := by
    -- ∂∂ = 0 gives a trivial bound for the boundary of the boundary.
    cases k with
    | zero =>
      trivial
    | succ k' =>
      refine ⟨0, ?_⟩
      intro ω
      -- (∂T)(dω) = T(d(dω)) = 0
      have hdd : smoothExtDeriv (smoothExtDeriv ω) = 0 := smoothExtDeriv_extDeriv ω
      -- T(0) = 0
      have h0 : T.toFun 0 = 0 := map_zero' T
      -- conclude
      simp [hdd, h0]

def isCycle (T : Current n X (k + 1)) : Prop := T.boundary = 0

/-- Degree-uniform cycle predicate for currents.

For degree `0`, there is no boundary operator, so every `0`-current is treated as a cycle.
For positive degree, this agrees with `Current.isCycle`. -/
def isCycleAt : {k : ℕ} → Current n X k → Prop
  | 0, _ => True
  | _ + 1, T => Current.isCycle T

@[simp] theorem isCycleAt_zero (T : Current n X 0) : T.isCycleAt := trivial

@[simp] theorem isCycleAt_succ_iff (T : Current n X (k + 1)) :
    T.isCycleAt ↔ Current.boundary T = 0 := Iff.rfl

/-- ∂∂ = 0: boundary of boundary is zero. -/
theorem boundary_boundary (T : Current n X (k + 2)) : (boundary (boundary T)) = 0 := by
  ext ω; show T.toFun (smoothExtDeriv (smoothExtDeriv ω)) = 0
  rw [smoothExtDeriv_extDeriv]
  exact map_zero' T

/-- **Boundary is additive**. -/
theorem boundary_add (S T : Current n X (k + 1)) : boundary (S + T) = boundary S + boundary T := by
  ext ω; rfl

/-- **Boundary of negation**. -/
theorem boundary_neg (T : Current n X (k + 1)) : boundary (-T) = -(boundary T) := by
  ext ω; rfl

theorem boundary_sub (S T : Current n X (k + 1)) : boundary (S - T) = boundary S - boundary T := by
  ext ω; rfl

@[simp] theorem boundary_toFun (T : Current n X (k + 1)) (ω : SmoothForm n X k) :
    (boundary T).toFun ω = T.toFun (smoothExtDeriv ω) := by
  rfl

theorem support_boundary_subset {n k : ℕ} {X : Type*}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (T : Current n X (k + 1)) :
    support (n := n) (X := X) (k := k) (boundary T) ⊆ support T := by
  classical
  intro x hx
  by_contra h
  have hxT : x ∉ support T := by simpa using h
  rcases (by
    simpa [support] using hxT) with ⟨U, hU, hzero, hxU⟩
  have hzero' :
      ∀ ω : SmoothForm n X k,
        HasCompactSupport ω.as_alternating →
          tsupport ω.as_alternating ⊆ U → (boundary T).toFun ω = 0 := by
    intro ω hcomp hsub
    have hcompact : IsCompact (tsupport ω.as_alternating) := by
      simpa [HasCompactSupport] using hcomp
    have hcompact' :
        IsCompact (tsupport (smoothExtDeriv ω).as_alternating) :=
      IsCompact.of_isClosed_subset hcompact (isClosed_tsupport _)
        (smoothExtDeriv_tsupport_subset (ω := ω))
    have hcomp' : HasCompactSupport (smoothExtDeriv ω).as_alternating := by
      simpa [HasCompactSupport] using hcompact'
    have hsub' :
        tsupport (smoothExtDeriv ω).as_alternating ⊆ U :=
      (smoothExtDeriv_tsupport_subset (ω := ω)).trans hsub
    have hT0 := hzero (smoothExtDeriv ω) hcomp' hsub'
    simpa [boundary_toFun] using hT0
  have hxUnion :
      x ∈ ⋃ (U : Set X) (_hU : IsOpen U)
        (_hzero :
          ∀ ω : SmoothForm n X k,
            HasCompactSupport ω.as_alternating →
              tsupport ω.as_alternating ⊆ U → (boundary T).toFun ω = 0),
        U := by
    refine Set.mem_iUnion_of_mem U ?_
    refine Set.mem_iUnion_of_mem hU ?_
    refine Set.mem_iUnion_of_mem hzero' ?_
    exact hxU
  have hxNot : x ∉ support (n := n) (X := X) (k := k) (boundary T) := by
    intro hxSupp
    exact hxSupp hxUnion
  exact hxNot hx

end Current

/-! ## Integration Currents via Hausdorff Measure

This section defines integration currents using Hausdorff measure.

### Mathematical Definition (Federer, 1969)

For a k-rectifiable set Z ⊆ X with orientation θ, the integration current [Z] is defined by:
  `[Z](ω) = ∫_Z ⟨ω, θ⟩ dH^k`
where:
- `H^k` is k-dimensional Hausdorff measure
- `θ : Z → Λ^k(T_x X)` is the orienting k-vector field
- `⟨ω, θ⟩` is the pairing of the k-form ω with the k-vector θ

### Implementation Strategy

Since full Hausdorff measure integration on manifolds requires substantial infrastructure,
we use a **data-carrying approach**:

1. `IntegrationData` bundles a set with its integration function and proofs
2. `integration_current` is defined via this data
3. The structure ensures all Current axioms are satisfied

This separates the *interface* (complete) from *implementation* (requires GMT).

### References
- [H. Federer, "Geometric Measure Theory", Springer 1969, §4.1-4.2]
- [F. Morgan, "Geometric Measure Theory: A Beginner's Guide", Academic Press 2016]
- [H. Federer and W.H. Fleming, "Normal and integral currents", Ann. Math. 72 (1960)]
-/

/-! ## Real Hausdorff Integration Infrastructure (Agent 5)

This section implements the mathematical infrastructure for integrating differential forms
against Hausdorff measure on rectifiable sets. This is the core of Agent 5's Clay-readiness work.

### Mathematical Background

For a k-dimensional oriented rectifiable set Z in an n-dimensional manifold X, the
**integration current** `[Z]` is defined by:

  `[Z](ω) = ∫_Z ⟨ω(x), τ(x)⟩ dH^k(x)`

where:
- `H^k` is the k-dimensional Hausdorff measure
- `τ(x)` is the orienting unit simple k-vector at x ∈ Z
- `⟨ω(x), τ(x)⟩` is the canonical pairing of a k-form with a k-vector

### Key Components

1. **`OrientedRectifiableSetData`**: Bundles a set with its orientation and Hausdorff measure
2. **`formVectorPairing`**: The pairing `⟨ω, τ⟩` of forms with k-vectors
3. **`hausdorffIntegrate`**: Integration of a form against Hausdorff measure on the set

### Stokes Property

For a rectifiable set Z with rectifiable boundary ∂Z:
  `[Z](dω) = [∂Z](ω)`

Therefore: `|[Z](dω)| ≤ mass(∂Z) · ‖ω‖`, giving `M = mass(∂Z)` as the Stokes constant.
-/

open MeasureTheory

/-- **Orienting k-vector** at a point.
    In a 2n-dimensional complex manifold, a real k-vector is an element of Λ^k(T_x X).
    For an oriented k-dimensional submanifold, this is the unit tangent k-vector.

    **Mathematical Definition**: τ ∈ Λ^k(T_x X) with |τ| = 1.

    **Implementation**: Currently represented as a function from points to ℝ.
    In a full implementation, this would be a section of the k-th exterior power of TX. -/
structure OrientingKVector (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  /-- The carrier set on which the orientation is defined -/
  support : Set X
  /-- The orienting k-vector field.
      Represented as a map to k-tuples of tangent vectors.
      The value at x represents v₁ ∧ ... ∧ vₖ. -/
  orientation : X → (Fin k → TangentModel n)
  /-- The orientation is unit at points in the support.
      (Norm definition for k-vectors would go here). -/
  unit_norm : ∀ x ∈ support, ‖orientation x‖ = 1

/-- **Form-Vector Pairing** (Federer, 1969).
    The canonical pairing of a k-form ω with a k-vector τ at a point x.

    **Mathematical Definition**: `⟨ω(x), τ(x)⟩ = ω_x(τ(x))`

    For a simple k-vector τ = v₁ ∧ ... ∧ v_k:
      `⟨ω, τ⟩ = ω(v₁, ..., v_k)`

    **Implementation**: Currently uses the fiber evaluation and orientation.
    In full development, this would properly contract the form with the k-vector.

    Reference: [H. Federer, "Geometric Measure Theory", 1969, §1.5.1]. -/
noncomputable def formVectorPairing {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (ω : SmoothForm n X k) (τ : OrientingKVector n X k) (x : X) : ℂ :=
  -- Evaluate the alternating form on the k-tuple of vectors
  (ω.as_alternating x) (τ.orientation x)

/-- formVectorPairing is additive in the form argument. -/
theorem formVectorPairing_add {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (ω₁ ω₂ : SmoothForm n X k) (τ : OrientingKVector n X k) (x : X) :
    formVectorPairing (ω₁ + ω₂) τ x = formVectorPairing ω₁ τ x + formVectorPairing ω₂ τ x := by
  simp only [formVectorPairing, SmoothForm.add_apply]
  -- FiberAlt is ContinuousAlternatingMap, addition is pointwise
  rfl

/-- formVectorPairing is scalar-multiplicative in the form argument. -/
theorem formVectorPairing_smul {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (c : ℂ) (ω : SmoothForm n X k) (τ : OrientingKVector n X k) (x : X) :
    formVectorPairing (c • ω) τ x = c * formVectorPairing ω τ x := by
  simp only [formVectorPairing, SmoothForm.smul_apply]
  rfl

theorem formVectorPairing_eq_zero_of_not_mem_tsupport {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (ω : SmoothForm n X k) (τ : OrientingKVector n X k) {x : X}
    (hx : x ∉ tsupport ω.as_alternating) : formVectorPairing ω τ x = 0 := by
  have hx_support : x ∉ Function.support ω.as_alternating := by
    intro hx_support
    exact hx (subset_tsupport _ hx_support)
  have hzero : ω.as_alternating x = 0 := by
    by_contra h
    have : x ∈ Function.support ω.as_alternating := by
      simpa [Function.mem_support, h] using h
    exact hx_support this
  simp [formVectorPairing, hzero]

/-- **Oriented Rectifiable Set Data** (Federer-Fleming, 1960).
    Bundles a k-dimensional rectifiable set with its orientation and Hausdorff measure.

    **Mathematical Definition**: An oriented k-rectifiable set is a triple (Z, τ, H^k|_Z) where:
    - Z ⊆ X is H^k-rectifiable (covered by countably many Lipschitz images of ℝ^k)
    - τ : Z → Λ^k(TX) is a measurable orienting k-vector field with |τ| = 1 H^k-a.e.
    - H^k|_Z is the restriction of k-dimensional Hausdorff measure to Z

    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", Ann. Math. 72 (1960)]. -/
structure OrientedRectifiableSetData (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] where
  /-- The underlying set -/
  carrier : Set X
  /-- The orienting k-vector field -/
  orientation : OrientingKVector n X k
  /-- The orientation is defined on the carrier -/
  orientation_support : orientation.support = carrier
  /-- The carrier is measurable. In GMT, rectifiable sets are (Hausdorff) measurable. -/
  carrier_measurable : MeasurableSet carrier
  /-- The orientation map is measurable (a.e. in the classical theory; we record it as measurable data). -/
  orientation_measurable : Measurable orientation.orientation
  /-- The k-dimensional Hausdorff measure restricted to the carrier.
      In Mathlib: μH[k] is the k-dimensional Hausdorff measure. -/
  measure : Measure X
  /-- Finite mass: the total Hausdorff measure of the set is finite -/
  finite_mass : measure carrier < ⊤
  /-- Boundary data: the (k-1)-dimensional boundary with its measure -/
  boundary_carrier : Set X
  boundary_measure : Measure X
  /-- The boundary has finite mass -/
  boundary_finite : boundary_measure boundary_carrier < ⊤
  /-- Integrability of the pairing.
      Smooth forms on compact manifolds are bounded, and the measure is finite,
      so this should be provable. But we include it as a field to avoid
      rebuilding the boundedness infrastructure. -/
  integrable_pairing : ∀ (ω : SmoothForm n X k),
    Integrable (fun x => formVectorPairing ω orientation x) (measure.restrict carrier)
  /-- The pairing is bounded by comass.
      This follows from the definition of comass and the fact that orientation is unit simple. -/
  pairing_le_comass : ∀ (ω : SmoothForm n X k), ∀ x ∈ carrier,
    ‖formVectorPairing ω orientation x‖ ≤ comass ω
  /-- **Stokes bound** (rectifiable Stokes inequality).

      This is the analytic heart of Stokes' theorem in GMT form:
      \(|\int_Z dω| \le \mathrm{mass}(\partial Z)\,\|ω\|\).

      We record it directly at the data level; proving it for the intended geometric objects
      is part of the remaining GMT formalization work. -/
  stokes_bound :
    match k with
    | 0 => True
    | k' + 1 =>
        ∀ ω : SmoothForm n X k',
          |(∫ x in carrier,
              formVectorPairing (smoothExtDeriv ω) orientation x ∂measure).re|
            ≤ (boundary_measure boundary_carrier).toReal * ‖ω‖

/-- **Hausdorff Integration** of a differential form over an oriented rectifiable set.

    **Mathematical Definition**:
      `∫_Z ω = ∫_Z ⟨ω(x), τ(x)⟩ dH^k(x)`

    **Implementation**: Combines form-vector pairing with integration against measure.
    Currently uses the product of orientation with comass as a proxy for the pairing.

    Reference: [H. Federer, "Geometric Measure Theory", 1969, §4.1.7]. -/
noncomputable def hausdorffIntegrate {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X]
    (data : OrientedRectifiableSetData n X k) (ω : SmoothForm n X k) : ℝ :=
  -- Real implementation: ∫_Z ⟨ω(x), τ(x)⟩ dH^k(x)
  -- We take the real part since Currents are defined as real-valued functionals
  (∫ x in data.carrier, formVectorPairing ω data.orientation x ∂data.measure).re

theorem hausdorffIntegrate_eq_zero_of_tsupport_subset {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X]
    (data : OrientedRectifiableSetData n X k) {U : Set X} (ω : SmoothForm n X k)
    (hU : tsupport ω.as_alternating ⊆ U) (hdis : Disjoint U data.carrier) :
    hausdorffIntegrate (n := n) (X := X) (k := k) data ω = 0 := by
  have hzero : ∀ x, x ∈ data.carrier → formVectorPairing ω data.orientation x = 0 := by
    intro x hxC
    have hxU : x ∉ U := by
      intro hxU
      exact (Set.disjoint_left.mp hdis) hxU hxC
    have hx_tsupp : x ∉ tsupport ω.as_alternating := by
      intro hx
      exact hxU (hU hx)
    simpa using (formVectorPairing_eq_zero_of_not_mem_tsupport (ω := ω) (τ := data.orientation) (x := x) hx_tsupp)
  have hzero_ae :
      ∀ᵐ x ∂data.measure, x ∈ data.carrier → formVectorPairing ω data.orientation x = 0 := by
    exact Filter.Eventually.of_forall hzero
  have hzero_restrict :
      ∀ᵐ x ∂data.measure.restrict data.carrier,
        formVectorPairing ω data.orientation x = 0 := by
    exact
      (MeasureTheory.ae_restrict_iff'
        (μ := data.measure) (s := data.carrier)
        (p := fun x => formVectorPairing ω data.orientation x = 0)
        data.carrier_measurable).2 hzero_ae
  have hzero_int :
      (∫ x in data.carrier, formVectorPairing ω data.orientation x ∂data.measure) = 0 := by
    simpa using (MeasureTheory.integral_eq_zero_of_ae hzero_restrict)
  simp [hausdorffIntegrate, hzero_int]

/-- **Mass of an Oriented Rectifiable Set**.
    The k-dimensional Hausdorff measure of the set.

    **Mathematical Definition**: mass(Z) = H^k(Z)

    Reference: [H. Federer, "Geometric Measure Theory", 1969, §4.1.7]. -/
noncomputable def OrientedRectifiableSetData.mass {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X]
    (data : OrientedRectifiableSetData n X k) : ℝ :=
  (data.measure data.carrier).toReal

/-- **Boundary Mass of an Oriented Rectifiable Set**.
    The (k-1)-dimensional Hausdorff measure of the boundary.

    **Mathematical Definition**: mass(∂Z) = H^{k-1}(∂Z)

    Reference: [H. Federer, "Geometric Measure Theory", 1969, §4.5.5]. -/
noncomputable def OrientedRectifiableSetData.bdryMass {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X]
    (data : OrientedRectifiableSetData n X k) : ℝ :=
  (data.boundary_measure data.boundary_carrier).toReal

/-- **Hausdorff integration is linear** (over ℝ).

    This is the key property allowing currents to act as linear functionals on forms.

    Proof uses:
    - formVectorPairing_add: pairing is additive
    - SmoothForm.smul_real_apply: real scalar multiplication
    - Bochner integral linearity from Mathlib -/
theorem hausdorffIntegrate_linear {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X]
    (data : OrientedRectifiableSetData n X k) (c : ℝ) (ω₁ ω₂ : SmoothForm n X k) :
    hausdorffIntegrate data (c • ω₁ + ω₂) = c * hausdorffIntegrate data ω₁ + hausdorffIntegrate data ω₂ := by
  -- Follows from Bochner integral linearity + integrability
  -- Key lemmas: integral_add, integral_smul, data.integrable_pairing
  let μ : Measure X := data.measure.restrict data.carrier

  have h₁ : Integrable (fun x => formVectorPairing ω₁ data.orientation x) μ := by
    simpa [μ] using data.integrable_pairing ω₁
  have h₂ : Integrable (fun x => formVectorPairing ω₂ data.orientation x) μ := by
    simpa [μ] using data.integrable_pairing ω₂
  have h₁s : Integrable (fun x => (c : ℂ) * formVectorPairing ω₁ data.orientation x) μ := by
    -- (c:ℂ) * f = (c:ℂ) • f
    simpa [smul_eq_mul] using (h₁.smul (c : ℂ))

  have hI :
      (∫ x in data.carrier, formVectorPairing (c • ω₁ + ω₂) data.orientation x ∂data.measure) =
        (c : ℂ) * (∫ x in data.carrier, formVectorPairing ω₁ data.orientation x ∂data.measure) +
          (∫ x in data.carrier, formVectorPairing ω₂ data.orientation x ∂data.measure) := by
    have h_pair :
        (fun x => formVectorPairing (c • ω₁ + ω₂) data.orientation x) =
          (fun x => (c : ℂ) * formVectorPairing ω₁ data.orientation x + formVectorPairing ω₂ data.orientation x) := by
      funext x
      have hadd :=
        formVectorPairing_add (ω₁ := (c • ω₁)) (ω₂ := ω₂) (τ := data.orientation) x
      have hsmul :
          formVectorPairing (c • ω₁) data.orientation x =
            (c : ℂ) * formVectorPairing ω₁ data.orientation x := by
        simpa using
          (formVectorPairing_smul (c := (c : ℂ)) (ω := ω₁) (τ := data.orientation) (x := x))
      simpa [hsmul, smul_eq_mul] using hadd

    have :
        (∫ x in data.carrier, formVectorPairing (c • ω₁ + ω₂) data.orientation x ∂data.measure) =
          (∫ x, ((c : ℂ) * formVectorPairing ω₁ data.orientation x + formVectorPairing ω₂ data.orientation x) ∂μ) := by
      simp [μ, h_pair]

    calc
      (∫ x in data.carrier, formVectorPairing (c • ω₁ + ω₂) data.orientation x ∂data.measure)
          = (∫ x, ((c : ℂ) * formVectorPairing ω₁ data.orientation x + formVectorPairing ω₂ data.orientation x) ∂μ) := this
      _ = (∫ x, (c : ℂ) * formVectorPairing ω₁ data.orientation x ∂μ) +
            (∫ x, formVectorPairing ω₂ data.orientation x ∂μ) := by
              simpa using (integral_add (μ := μ) h₁s h₂)
      _ = (c : ℂ) * (∫ x, formVectorPairing ω₁ data.orientation x ∂μ) +
            (∫ x, formVectorPairing ω₂ data.orientation x ∂μ) := by
              -- integral_smul for the scalar (c:ℂ)
              simpa [smul_eq_mul] using
                congrArg (fun z => z + (∫ x, formVectorPairing ω₂ data.orientation x ∂μ))
                  (integral_smul (μ := μ) (c := (c : ℂ)) (f := fun x => formVectorPairing ω₁ data.orientation x))
      _ = (c : ℂ) * (∫ x in data.carrier, formVectorPairing ω₁ data.orientation x ∂data.measure) +
            (∫ x in data.carrier, formVectorPairing ω₂ data.orientation x ∂data.measure) := by
              rfl

  -- take real parts
  simp [hausdorffIntegrate, hI, Complex.add_re, Complex.mul_re]

/-- **Integration is bounded by mass times comass** (Mass-Comass Duality).

    **Mathematical Statement**: `|∫_Z ω| ≤ mass(Z) · comass(ω)`

    This is a fundamental inequality in Geometric Measure Theory.

    Reference: [H. Federer, "Geometric Measure Theory", 1969, §4.1.7]. -/
theorem hausdorffIntegrate_bound {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X]
    (data : OrientedRectifiableSetData n X k) (ω : SmoothForm n X k) :
    |hausdorffIntegrate data ω| ≤ data.mass * comass ω := by
  -- Mass-comass duality: |∫ ⟨ω,τ⟩| ≤ mass * comass
  -- Key lemmas: norm_integral_le_integral_norm, data.pairing_le_comass
  classical
  let μ : Measure X := data.measure.restrict data.carrier

  -- The restricted measure is finite since `data.finite_mass` is exactly `measure carrier < ⊤`.
  haveI : Fact (data.measure data.carrier < ⊤) := ⟨data.finite_mass⟩
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance

  -- Integrability of the pairing on the restricted measure.
  have hint : Integrable (fun x => formVectorPairing ω data.orientation x) μ := by
    simpa [μ] using data.integrable_pairing ω
  have hnorm_int : Integrable (fun x => ‖formVectorPairing ω data.orientation x‖) μ :=
    hint.norm

  -- a.e. bound of the integrand norm by `comass ω`
  have h_ae :
      (fun x => ‖formVectorPairing ω data.orientation x‖) ≤ᶠ[ae μ] fun _ => comass ω := by
    -- on the carrier this holds pointwise, and `μ = data.measure.restrict data.carrier`
    have hP :
        ∀ᵐ x ∂μ, ‖formVectorPairing ω data.orientation x‖ ≤ comass ω := by
      -- `ae_restrict_of_forall_mem` needs measurability of the carrier.
      have hP' :
          ∀ᵐ x ∂data.measure.restrict data.carrier, ‖formVectorPairing ω data.orientation x‖ ≤ comass ω :=
        MeasureTheory.ae_restrict_of_forall_mem (μ := data.measure) (s := data.carrier)
          data.carrier_measurable (fun x hx => data.pairing_le_comass ω x hx)
      simpa [μ] using hP'
    exact hP

  -- Main estimate
  -- 1) |Re ∫ f| ≤ ‖∫ f‖
  -- 2) ‖∫ f‖ ≤ ∫ ‖f‖
  -- 3) ∫ ‖f‖ ≤ ∫ (comass ω) = mass * comass ω
  have h_step1 :
      |(∫ x in data.carrier, formVectorPairing ω data.orientation x ∂data.measure).re|
        ≤ ‖∫ x in data.carrier, formVectorPairing ω data.orientation x ∂data.measure‖ :=
    Complex.abs_re_le_norm _
  have h_step2 :
      ‖∫ x in data.carrier, formVectorPairing ω data.orientation x ∂data.measure‖
        ≤ ∫ x in data.carrier, ‖formVectorPairing ω data.orientation x‖ ∂data.measure := by
    -- set integrals are just integrals over the restricted measure
    simpa [μ] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := μ)
        (fun x => formVectorPairing ω data.orientation x))

  have h_step3 :
      (∫ x in data.carrier, ‖formVectorPairing ω data.orientation x‖ ∂data.measure)
        ≤ ∫ x in data.carrier, (comass ω) ∂data.measure := by
    -- integral_mono_ae on the restricted measure μ
    simpa [μ] using
      (MeasureTheory.integral_mono_ae (μ := μ) hnorm_int (MeasureTheory.integrable_const (μ := μ) (comass ω)) h_ae)

  -- compute the constant integral: ∫_carrier (comass ω) = mass * comass ω
  have h_const :
      (∫ x in data.carrier, (comass ω) ∂data.measure) = data.mass * comass ω := by
    -- unfold `data.mass = (data.measure data.carrier).toReal` and use `integral_const`
    simp [OrientedRectifiableSetData.mass, μ, MeasureTheory.integral_const, smul_eq_mul, Measure.real]

  -- combine
  have :
      |hausdorffIntegrate data ω| ≤ data.mass * comass ω := by
    -- unfold hausdorffIntegrate and chain the inequalities
    dsimp [hausdorffIntegrate]
    calc
      |(∫ x in data.carrier, formVectorPairing ω data.orientation x ∂data.measure).re|
          ≤ ‖∫ x in data.carrier, formVectorPairing ω data.orientation x ∂data.measure‖ := h_step1
      _ ≤ ∫ x in data.carrier, ‖formVectorPairing ω data.orientation x‖ ∂data.measure := h_step2
      _ ≤ ∫ x in data.carrier, (comass ω) ∂data.measure := h_step3
      _ = data.mass * comass ω := h_const
  simpa [hausdorffIntegrate] using this

-- NOTE: OrientedRectifiableSetData.toIntegrationData is defined after IntegrationData structure

/-! ### Closed Submanifold Integration

For closed submanifolds (compact without boundary), the Stokes bound is trivially satisfied
with M = 0 since there is no boundary. This is the key case for the Hodge conjecture. -/

/-- **Closed Submanifold Data** (Griffiths-Harris).
    A closed (compact, boundaryless) k-dimensional complex submanifold.

    For the Hodge conjecture, these arise as:
    - Zero loci of sections of line bundles
    - Images of holomorphic maps from compact manifolds
    - Components of algebraic cycles

    Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", Ch. 0-1]. -/
structure ClosedSubmanifoldData (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] where
  /-- The underlying set -/
  carrier : Set X
  /-- The carrier is measurable. -/
  carrier_measurable : MeasurableSet carrier
  /-- The orienting k-vector field -/
  orientation : OrientingKVector n X k
  /-- Orientation matches carrier -/
  orientation_support : orientation.support = carrier
  /-- The orientation map is measurable. -/
  orientation_measurable : Measurable orientation.orientation
  /-- The Hausdorff measure -/
  measure : Measure X
  /-- Finite mass -/
  finite_mass : measure carrier < ⊤
  /-- **Stokes on closed submanifolds**: the integral of an exact form vanishes.

      In classical terms: \(\int_Z dω = \int_{\partial Z} ω = 0\) since \(\partial Z = \emptyset\).
      We record the vanishing of the real-part integral that defines `hausdorffIntegrate`. -/
  stokes_integral_exact_zero :
    match k with
    | 0 => True
    | k' + 1 =>
        ∀ ω : SmoothForm n X k',
          (∫ x in carrier,
              formVectorPairing (smoothExtDeriv ω) orientation x ∂measure).re = 0

/-- Transport `ClosedSubmanifoldData` across a degree equality. -/
noncomputable def ClosedSubmanifoldData.cast {n : ℕ} {X : Type*} {k k' : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X]
    (h : k = k') (data : ClosedSubmanifoldData n X k) :
    ClosedSubmanifoldData n X k' := by
  cases h
  exact data

@[simp] theorem ClosedSubmanifoldData.cast_carrier {n : ℕ} {X : Type*} {k k' : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X]
    (h : k = k') (data : ClosedSubmanifoldData n X k) :
    (ClosedSubmanifoldData.cast (n := n) (X := X) (k := k) (k' := k') h data).carrier =
      data.carrier := by
  cases h
  rfl

/-- Convert closed submanifold data to oriented rectifiable set data.
    The key point: boundary_carrier = ∅ and boundary_measure = 0. -/
noncomputable def ClosedSubmanifoldData.toOrientedData {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X]
    (data : ClosedSubmanifoldData n X k) : OrientedRectifiableSetData n X k where
  carrier := data.carrier
  orientation := data.orientation
  orientation_support := data.orientation_support
  carrier_measurable := data.carrier_measurable
  orientation_measurable := data.orientation_measurable
  measure := data.measure
  finite_mass := data.finite_mass
  boundary_carrier := ∅  -- No boundary
  boundary_measure := 0  -- Zero measure on empty set
  boundary_finite := by simp
  integrable_pairing := fun ω => by
    classical
    let μ : Measure X := data.measure.restrict data.carrier
    haveI : Fact (data.measure data.carrier < ⊤) := ⟨data.finite_mass⟩
    haveI : IsFiniteMeasure μ := by
      dsimp [μ]
      infer_instance

    -- Measurability of the pairing function via continuity of evaluation.
    have h_meas :
        Measurable (fun x : X => formVectorPairing ω data.orientation x) := by
      -- evaluation map on (map, vector) is continuous, hence measurable
      have h_eval :
          Measurable (fun p : (FiberAlt n k) × (Fin k → TangentModel n) => p.1 p.2) :=
        (ContinuousEval.continuous_eval : Continuous fun p : (FiberAlt n k) × (Fin k → TangentModel n) => p.1 p.2).measurable
      have h_pair :
          Measurable (fun x : X => (ω.as_alternating x, data.orientation.orientation x)) :=
        Measurable.prodMk (ω.is_smooth.continuous.measurable) data.orientation_measurable
      simpa [formVectorPairing] using h_eval.comp h_pair

    have h_ae :
        (∀ᵐ x ∂μ, ‖formVectorPairing ω data.orientation x‖ ≤ comass ω) := by
      -- pointwise on the carrier, hence a.e. on the restricted measure
      have h0 :
          ∀ᵐ x ∂data.measure.restrict data.carrier,
            ‖formVectorPairing ω data.orientation x‖ ≤ comass ω :=
        MeasureTheory.ae_restrict_of_forall_mem (μ := data.measure) (s := data.carrier)
          data.carrier_measurable (fun x hx => by
            -- same proof as `pairing_le_comass` below, specialized to this ω and x
            have hx' : x ∈ data.orientation.support := by
              simpa [data.orientation_support] using hx
            have hun : ‖data.orientation.orientation x‖ = 1 := data.orientation.unit_norm x hx'
            have hop :
                ‖(ω.as_alternating x) (data.orientation.orientation x)‖ ≤
                  ‖ω.as_alternating x‖ * ∏ i : Fin k, ‖data.orientation.orientation x i‖ := by
              simpa using
                (ContinuousAlternatingMap.le_opNorm (ω.as_alternating x) (data.orientation.orientation x))
            have hcomp : ∀ i : Fin k, ‖data.orientation.orientation x i‖ ≤ 1 := by
              intro i
              have hi : ‖data.orientation.orientation x i‖ ≤ ‖data.orientation.orientation x‖ :=
                norm_le_pi_norm (data.orientation.orientation x) i
              simpa [hun] using hi
            have hprod : (∏ i : Fin k, ‖data.orientation.orientation x i‖) ≤ (1 : ℝ) := by
              classical
              simpa using (Finset.prod_le_one (s := (Finset.univ : Finset (Fin k)))
                (f := fun i : Fin k => ‖data.orientation.orientation x i‖)
                (h0 := by intro i hi; exact norm_nonneg _)
                (h1 := by intro i hi; simpa using hcomp i))
            have h1 :
                ‖(ω.as_alternating x) (data.orientation.orientation x)‖ ≤ ‖ω.as_alternating x‖ := by
              have hmul := mul_le_mul_of_nonneg_left hprod (norm_nonneg (ω.as_alternating x))
              have hmul' :
                  ‖ω.as_alternating x‖ * (∏ i : Fin k, ‖data.orientation.orientation x i‖) ≤ ‖ω.as_alternating x‖ := by
                simpa [_root_.mul_one] using hmul
              exact le_trans hop hmul'
            have hcom : ‖ω.as_alternating x‖ ≤ comass ω := by
              unfold comass
              apply le_csSup (comass_bddAbove (n := n) (X := X) (α := ω))
              exact ⟨x, rfl⟩
            simpa [formVectorPairing] using le_trans h1 hcom)
      simpa [μ] using h0

    -- Use boundedness on a finite measure space to get integrability.
    refine MeasureTheory.Integrable.of_bound (μ := μ) (h_meas.aestronglyMeasurable) (comass ω) ?_
    simpa using h_ae
  pairing_le_comass := fun ω x hx => by
    -- Bound by the operator norm, then by `comass` via `le_csSup`.
    have hx' : x ∈ data.orientation.support := by
      simpa [data.orientation_support] using hx
    have hun : ‖data.orientation.orientation x‖ = 1 := data.orientation.unit_norm x hx'

    have hop :
        ‖(ω.as_alternating x) (data.orientation.orientation x)‖ ≤
          ‖ω.as_alternating x‖ * ∏ i : Fin k, ‖data.orientation.orientation x i‖ := by
      simpa using
        (ContinuousAlternatingMap.le_opNorm (ω.as_alternating x) (data.orientation.orientation x))

    have hcomp : ∀ i : Fin k, ‖data.orientation.orientation x i‖ ≤ 1 := by
      intro i
      have hi : ‖data.orientation.orientation x i‖ ≤ ‖data.orientation.orientation x‖ :=
        norm_le_pi_norm (data.orientation.orientation x) i
      simpa [hun] using hi

    have hprod : (∏ i : Fin k, ‖data.orientation.orientation x i‖) ≤ (1 : ℝ) := by
      classical
      simpa using (Finset.prod_le_one (s := (Finset.univ : Finset (Fin k)))
        (f := fun i : Fin k => ‖data.orientation.orientation x i‖)
        (h0 := by intro i hi; exact norm_nonneg _)
        (h1 := by intro i hi; simpa using hcomp i))

    have h1 :
        ‖(ω.as_alternating x) (data.orientation.orientation x)‖ ≤ ‖ω.as_alternating x‖ := by
      have hmul := mul_le_mul_of_nonneg_left hprod (norm_nonneg (ω.as_alternating x))
      have hmul' :
          ‖ω.as_alternating x‖ * (∏ i : Fin k, ‖data.orientation.orientation x i‖) ≤ ‖ω.as_alternating x‖ := by
        simpa [_root_.mul_one] using hmul
      exact le_trans hop hmul'

    have hcom : ‖ω.as_alternating x‖ ≤ comass ω := by
      unfold comass
      apply le_csSup (comass_bddAbove (n := n) (X := X) (α := ω))
      exact ⟨x, rfl⟩

    simpa [formVectorPairing] using le_trans h1 hcom
  stokes_bound := by
    cases k with
    | zero => trivial
    | succ k' =>
      intro ω
      -- `bdryMass` is computed from `boundary_measure` which is `0`, so the RHS is `0`.
      -- The LHS vanishes by the Stokes data recorded on the closed submanifold.
      have h0 :
          (∫ x in data.carrier,
              formVectorPairing (smoothExtDeriv ω) data.orientation x ∂data.measure).re = 0 := by
        simpa using (data.stokes_integral_exact_zero ω)
      -- Reduce both sides to `0 ≤ 0`.
      simp [h0]

/-- **Closed Submanifold has Zero Boundary Mass**.
    This is the key property for the Hodge conjecture. -/
theorem ClosedSubmanifoldData.bdryMass_zero {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X]
    (data : ClosedSubmanifoldData n X k) :
    data.toOrientedData.bdryMass = 0 := by
  unfold ClosedSubmanifoldData.toOrientedData OrientedRectifiableSetData.bdryMass
  simp

-- NOTE: ClosedSubmanifoldData.toIntegrationData is defined after IntegrationData structure

open MeasureTheory in
/-- **Integration Data** (Federer, 1969).
    Bundles a set Z with all the data needed to define an integration current:
    - The underlying set
    - The integration functional (defined via Hausdorff measure + orientation)
    - Proofs of linearity, continuity, and boundedness

    This structure allows us to define integration currents with proven properties
    while deferring the Hausdorff measure implementation details.

    Reference: [H. Federer, "Geometric Measure Theory", 1969, §4.1.7]. -/
structure IntegrationData (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] where
  /-- The underlying set being integrated over -/
  carrier : Set X
  /-- The integration functional: ω ↦ ∫_Z ω -/
  integrate : SmoothForm n X k → ℝ
  /-- Integration is linear -/
  integrate_linear : ∀ (c : ℝ) (ω₁ ω₂ : SmoothForm n X k),
    integrate (c • ω₁ + ω₂) = c * integrate ω₁ + integrate ω₂
  /-- Integration is bounded by comass norm -/
  integrate_bound : ∃ M : ℝ, ∀ ω : SmoothForm n X k, |integrate ω| ≤ M * ‖ω‖
  /-- Boundary mass: mass(∂Z), used for Stokes bound -/
  bdryMass : ℝ
  /-- Boundary mass is non-negative -/
  bdryMass_nonneg : bdryMass ≥ 0
  /-- **Stokes property**: for any form ω, the integral of dω is bounded by bdryMass · ‖ω‖.
      This is the shape needed for the `boundary_bound` field of `Current`.

      Note: In full GMT, only the case `k = k' + 1` is meaningful (integrating exact (k)-forms).
      We package it uniformly as a Prop so downstream constructions don't need to pattern-match
      on `k` (which can be a complex expression like `2 * (n - p)`).
  -/
  stokes_bound : ∀ {k' : ℕ} (hk : k = k' + 1) (ω : SmoothForm n X k'),
    |integrate (hk ▸ smoothExtDeriv ω)| ≤ bdryMass * ‖ω‖

/-- The empty set as integration data with zero integral. -/
noncomputable def IntegrationData.empty (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] : IntegrationData n X k where
  carrier := ∅
  integrate := fun _ => 0
  integrate_linear := by intros; ring
  integrate_bound := ⟨0, fun _ => by simp⟩
  bdryMass := 0
  bdryMass_nonneg := le_refl 0
  stokes_bound := fun {k'} hk' ω => by
    -- integrate := fun _ => 0, so integrate (smoothExtDeriv ω) = 0.
    -- The goal is |0| ≤ 0 * ‖ω‖ = 0 which is true.
    -- We need to use hk' : k = k' + 1 to typecheck (smoothExtDeriv ω : SmoothForm n X (k' + 1)).
    -- For the empty set, integrate is constant 0 regardless of degree.
    simp only [MulZeroClass.zero_mul, abs_zero, le_refl]

/-- Convert IntegrationData to a Current.
    This is the main constructor for integration currents. -/
noncomputable def IntegrationData.toCurrent {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (data : IntegrationData n X k) : Current n X k where
  toFun :=
    let f : SmoothForm n X k →ₗ[ℝ] ℝ :=
      { toFun := data.integrate
        map_add' := fun ω₁ ω₂ => by
          -- linearity with c = 1
          simpa [one_smul, _root_.one_mul] using (data.integrate_linear 1 ω₁ ω₂)
        map_smul' := fun r ω => by
          -- First, `integrate 0 = 0` follows from additivity at 0.
          have h0' := data.integrate_linear 1 (0 : SmoothForm n X k) (0 : SmoothForm n X k)
          have h0'' : data.integrate (0 : SmoothForm n X k) =
              data.integrate (0 : SmoothForm n X k) + data.integrate (0 : SmoothForm n X k) := by
            simpa [one_smul, _root_.one_mul] using h0'
          have h0 : data.integrate (0 : SmoothForm n X k) = 0 := by
            linarith
          -- Now use linearity with ω₂ = 0.
          have h := data.integrate_linear r ω 0
          simpa [add_zero, h0] using h }
    have hbound : ∃ C : ℝ, ∀ ω : SmoothForm n X k, ‖f ω‖ ≤ C * ‖ω‖ := by
      obtain ⟨M, hM⟩ := data.integrate_bound
      refine ⟨M, ?_⟩
      intro ω
      simpa [f, Real.norm_eq_abs] using (hM ω)
    f.mkContinuousOfExistsBound hbound
  boundary_bound := by
    cases k with
    | zero => trivial
    | succ k' =>
      -- Use the stokes_bound from data.
      refine ⟨data.bdryMass, ?_⟩
      intro ω
      exact data.stokes_bound rfl ω

/-- **Convert Oriented Rectifiable Set Data to IntegrationData**.
    This bridges the GMT structure with the Current infrastructure.

    The key properties:
    - `integrate` uses real Hausdorff integration
    - `bdryMass` is the actual boundary mass
    - `stokes_bound` follows from Stokes' theorem -/
noncomputable def OrientedRectifiableSetData.toIntegrationData {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (data : OrientedRectifiableSetData n X k) : IntegrationData n X k where
  carrier := data.carrier
  integrate := fun ω => hausdorffIntegrate data ω
  integrate_linear := fun c ω₁ ω₂ => hausdorffIntegrate_linear data c ω₁ ω₂
  integrate_bound := ⟨data.mass, fun ω => hausdorffIntegrate_bound data ω⟩
  bdryMass := data.bdryMass
  bdryMass_nonneg := by
    unfold OrientedRectifiableSetData.bdryMass
    exact ENNReal.toReal_nonneg
  stokes_bound := by
    intro k' hk' ω
    -- hk' : k = k' + 1, so data.stokes_bound applies.
    -- Stokes theorem for rectifiable sets (recorded in `data.stokes_bound`).
    -- data.stokes_bound has type: match k with | 0 => True | k' + 1 => ...
    -- Since k = k' + 1, the match evaluates to the non-trivial case.
    have hk_succ : k = Nat.succ k' := hk'
    cases hk_succ
    simpa [hausdorffIntegrate, OrientedRectifiableSetData.bdryMass] using data.stokes_bound ω

theorem support_orientedRectifiableCurrent_subset_closure {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (data : OrientedRectifiableSetData n X k) :
    Current.support (n := n) (X := X) (k := k) (data.toIntegrationData.toCurrent) ⊆
      closure data.carrier := by
  classical
  intro x hx
  by_contra hx'
  let U : Set X := (closure data.carrier)ᶜ
  have hUopen : IsOpen U := isClosed_closure.isOpen_compl
  have hxU : x ∈ U := by
    simpa [U] using hx'
  have hdis : Disjoint U data.carrier := by
    refine Set.disjoint_left.mpr ?_
    intro y hyU hyC
    have hyC' : y ∈ closure data.carrier := subset_closure hyC
    exact hyU hyC'
  have hzero :
      ∀ ω : SmoothForm n X k,
        HasCompactSupport ω.as_alternating →
          tsupport ω.as_alternating ⊆ U →
            (data.toIntegrationData.toCurrent).toFun ω = 0 := by
    intro ω _hcomp hsub
    have h :=
      hausdorffIntegrate_eq_zero_of_tsupport_subset (n := n) (X := X) (k := k)
        data ω hsub hdis
    -- unfold the current evaluation
    simp [IntegrationData.toCurrent, OrientedRectifiableSetData.toIntegrationData, h]
  have hxUnion :
      x ∈ ⋃ (U : Set X) (_hU : IsOpen U)
        (_hzero :
          ∀ ω : SmoothForm n X k,
            HasCompactSupport ω.as_alternating →
              tsupport ω.as_alternating ⊆ U → (data.toIntegrationData.toCurrent).toFun ω = 0),
        U := by
    refine Set.mem_iUnion_of_mem U ?_
    refine Set.mem_iUnion_of_mem hUopen ?_
    refine Set.mem_iUnion_of_mem hzero ?_
    exact hxU
  have hxNot : x ∉ Current.support (n := n) (X := X) (k := k) (data.toIntegrationData.toCurrent) := by
    intro hxSupp
    exact hxSupp hxUnion
  exact hxNot hx

theorem support_orientedRectifiableCurrent_subset {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (data : OrientedRectifiableSetData n X k) (hclosed : IsClosed data.carrier) :
    Current.support (n := n) (X := X) (k := k) (data.toIntegrationData.toCurrent) ⊆
      data.carrier := by
  have h :=
    support_orientedRectifiableCurrent_subset_closure (n := n) (X := X) (k := k) data
  simpa [hclosed.closure_eq] using h

/-- **Closed Submanifold to IntegrationData with Zero Boundary Mass**.
    The Stokes bound holds trivially with M = 0. -/
noncomputable def ClosedSubmanifoldData.toIntegrationData {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (data : ClosedSubmanifoldData n X k) : IntegrationData n X k where
  carrier := data.carrier
  -- Real: integration over closed submanifold using Hausdorff measure
  integrate := fun ω => hausdorffIntegrate data.toOrientedData ω
  integrate_linear := fun c ω₁ ω₂ => hausdorffIntegrate_linear data.toOrientedData c ω₁ ω₂
  integrate_bound := ⟨data.toOrientedData.mass, fun ω => hausdorffIntegrate_bound data.toOrientedData ω⟩
  bdryMass := 0  -- Closed submanifold has no boundary
  bdryMass_nonneg := le_refl 0
  stokes_bound := by
    intro k' hk' ω
    simp only [MulZeroClass.zero_mul]
    -- hk' : k = k' + 1, so k = Nat.succ k' and ω : SmoothForm n X k'.
    -- Substitute k = k' + 1 so that data.toOrientedData.stokes_bound reduces.
    cases hk'
    -- Now data : ClosedSubmanifoldData n X (k' + 1), and the match reduces.
    -- Reduce to the Stokes bound already recorded on `data.toOrientedData`.
    -- For a closed submanifold, the boundary measure is `0`, so |∫ dω| ≤ 0.
    have h := data.toOrientedData.stokes_bound ω
    have h' :
        |(∫ x in data.toOrientedData.carrier,
              formVectorPairing (smoothExtDeriv ω) data.toOrientedData.orientation x ∂data.toOrientedData.measure).re| ≤
          0 := by
      -- `data.toOrientedData.boundary_measure = 0` and `boundary_carrier = ∅`
      simpa [ClosedSubmanifoldData.toOrientedData, OrientedRectifiableSetData.bdryMass] using h
    -- Conclude by showing the integral real part is zero.
    have habs :
        |(∫ x in data.toOrientedData.carrier,
              formVectorPairing (smoothExtDeriv ω) data.toOrientedData.orientation x ∂data.toOrientedData.measure).re| = 0 :=
      le_antisymm h' (abs_nonneg _)
    have hz :
        (∫ x in data.toOrientedData.carrier,
              formVectorPairing (smoothExtDeriv ω) data.toOrientedData.orientation x ∂data.toOrientedData.measure).re = 0 :=
      (abs_eq_zero).1 habs
    -- The goal involves `integrate (smoothExtDeriv ω)` which is hausdorffIntegrate.
    -- We need to show the LHS is 0 (which implies |LHS| ≤ 0).
    -- By hz, the integral is 0, so |0| = 0 ≤ 0.
    simp only [hausdorffIntegrate]
    rw [hz]
    simp only [abs_zero, le_refl]

theorem support_closedSubmanifoldCurrent_subset_closure {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (data : ClosedSubmanifoldData n X k) :
    Current.support (n := n) (X := X) (k := k) (data.toIntegrationData.toCurrent) ⊆
      closure data.carrier := by
  classical
  intro x hx
  by_contra hx'
  let U : Set X := (closure data.carrier)ᶜ
  have hUopen : IsOpen U := isClosed_closure.isOpen_compl
  have hxU : x ∈ U := by
    simpa [U] using hx'
  have hdis : Disjoint U data.carrier := by
    refine Set.disjoint_left.mpr ?_
    intro y hyU hyC
    have hyC' : y ∈ closure data.carrier := subset_closure hyC
    exact hyU hyC'
  have hzero :
      ∀ ω : SmoothForm n X k,
        HasCompactSupport ω.as_alternating →
          tsupport ω.as_alternating ⊆ U →
            (data.toIntegrationData.toCurrent).toFun ω = 0 := by
    intro ω _hcomp hsub
    -- integrate over a set disjoint from the support of ω
    have h :=
      hausdorffIntegrate_eq_zero_of_tsupport_subset (n := n) (X := X) (k := k)
        data.toOrientedData ω hsub hdis
    -- unfold the current evaluation
    simp [IntegrationData.toCurrent, ClosedSubmanifoldData.toIntegrationData, h]
  have hxUnion :
      x ∈ ⋃ (U : Set X) (_hU : IsOpen U)
        (_hzero :
          ∀ ω : SmoothForm n X k,
            HasCompactSupport ω.as_alternating →
              tsupport ω.as_alternating ⊆ U → (data.toIntegrationData.toCurrent).toFun ω = 0),
        U := by
    refine Set.mem_iUnion_of_mem U ?_
    refine Set.mem_iUnion_of_mem hUopen ?_
    refine Set.mem_iUnion_of_mem hzero ?_
    exact hxU
  have hxNot : x ∉ Current.support (n := n) (X := X) (k := k) (data.toIntegrationData.toCurrent) := by
    intro hxSupp
    exact hxSupp hxUnion
  exact hxNot hx

theorem support_closedSubmanifoldCurrent_subset {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (data : ClosedSubmanifoldData n X k) (hclosed : IsClosed data.carrier) :
    Current.support (n := n) (X := X) (k := k) (data.toIntegrationData.toCurrent) ⊆
      data.carrier := by
  have h :=
    support_closedSubmanifoldCurrent_subset_closure (n := n) (X := X) (k := k) data
  simpa [hclosed.closure_eq] using h

/-- **Closed submanifold Stokes data** for a concrete carrier `Z`.

Compatibility-only wrapper: this packages a `ClosedSubmanifoldData` instance whose
carrier is `Z`, so older call sites can pass a set and a typeclass instance.

**Proof-track guidance**: prefer `ClosedSubmanifoldData` directly and thread it
explicitly through integration/Stokes arguments. -/
class ClosedSubmanifoldStokesData (n : ℕ) (X : Type*) (k : ℕ) (Z : Set X)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] where
  data : ClosedSubmanifoldData n X k
  carrier_eq : data.carrier = Z

/-- Compatibility-only constructor for `ClosedSubmanifoldStokesData`. -/
noncomputable def ClosedSubmanifoldStokesData.ofData {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (data : ClosedSubmanifoldData n X k) :
    ClosedSubmanifoldStokesData n X k data.carrier :=
  ⟨data, rfl⟩

/-- Compatibility-only conversion to `IntegrationData` (proof-track uses `data.toIntegrationData`). -/
noncomputable def ClosedSubmanifoldStokesData.toIntegrationData {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {Z : Set X} [ClosedSubmanifoldStokesData n X k Z] : IntegrationData n X k :=
  (ClosedSubmanifoldStokesData.data (n := n) (X := X) (k := k) (Z := Z)).toIntegrationData

theorem ClosedSubmanifoldStokesData.carrier_eq' {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {Z : Set X} [ClosedSubmanifoldStokesData n X k Z] :
    (ClosedSubmanifoldStokesData.toIntegrationData (n := n) (X := X) (k := k) (Z := Z)).carrier = Z := by
  simpa [ClosedSubmanifoldStokesData.toIntegrationData] using
    (ClosedSubmanifoldStokesData.carrier_eq (n := n) (X := X) (k := k) (Z := Z))

theorem ClosedSubmanifoldStokesData.support_subset_closure {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {Z : Set X} [ClosedSubmanifoldStokesData n X k Z] :
    Current.support (n := n) (X := X) (k := k)
        (ClosedSubmanifoldStokesData.toIntegrationData (n := n) (X := X) (k := k) (Z := Z)).toCurrent ⊆
      closure Z := by
  have h :=
    support_closedSubmanifoldCurrent_subset_closure (n := n) (X := X) (k := k)
      (ClosedSubmanifoldStokesData.data (n := n) (X := X) (k := k) (Z := Z))
  simpa [ClosedSubmanifoldStokesData.toIntegrationData,
    ClosedSubmanifoldStokesData.carrier_eq (n := n) (X := X) (k := k) (Z := Z)] using h

theorem ClosedSubmanifoldStokesData.support_subset {n : ℕ} {X : Type*} {k : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {Z : Set X} [ClosedSubmanifoldStokesData n X k Z] (hclosed : IsClosed Z) :
    Current.support (n := n) (X := X) (k := k)
        (ClosedSubmanifoldStokesData.toIntegrationData (n := n) (X := X) (k := k) (Z := Z)).toCurrent ⊆
      Z := by
  have h :=
    ClosedSubmanifoldStokesData.support_subset_closure (n := n) (X := X) (k := k) (Z := Z)
  simpa [hclosed.closure_eq] using h

/-!
NOTE (no-gotchas): The legacy Set-based integration plumbing (`setIntegral`,
`StokesTheoremData`, `integration_current`, and related boundary-mass blueprint stubs)
was removed. The proof track uses the data-based integration layer
(`OrientedRectifiableSetData` / `ClosedSubmanifoldData` → `IntegrationData` → `Current`).

The `ClosedSubmanifoldStokesData` defined above is a **data wrapper** around
`ClosedSubmanifoldData` that records the carrier set explicitly; it is *not* the
old Set-based stub interface. -/

end
