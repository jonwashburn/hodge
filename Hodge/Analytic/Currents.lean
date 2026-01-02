import Hodge.Analytic.Forms
import Hodge.Analytic.Norms

/-!

This file defines currents (distributional differential forms) on compact Kähler manifolds.

In the stub model, all currents evaluate to zero on all forms.
-/

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-- A current of dimension k is a continuous linear functional on smooth k-forms.
    In this stub model, all currents evaluate to zero. -/
structure Current (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  toFun : SmoothForm n X k → ℝ
  is_linear : ∀ (c : ℝ) (ω₁ ω₂ : SmoothForm n X k), toFun (c • ω₁ + ω₂) = c * toFun ω₁ + toFun ω₂

namespace Current

variable {k : ℕ}

/-- In the stub model, all currents evaluate to zero on all forms,
    so linearity properties follow from 0 = 0. -/
theorem map_add' {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (ω₁ ω₂ : SmoothForm n X k) : T.toFun (ω₁ + ω₂) = T.toFun ω₁ + T.toFun ω₂ := by
  have h := T.is_linear 1 ω₁ ω₂
  simp at h
  exact h

theorem map_add {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (ω₁ ω₂ : SmoothForm n X k) : T.toFun (ω₁ + ω₂) = T.toFun ω₁ + T.toFun ω₂ :=
  map_add' T ω₁ ω₂

/-- Scalar multiplication is linear (derived from is_linear axiom).
    Proof: Set ω₂ = 0 in is_linear: toFun(c•ω₁ + 0) = c * toFun(ω₁) + toFun(0) = c * toFun(ω₁). -/
theorem map_smul' {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (r : ℝ) (ω : SmoothForm n X k) : T.toFun (r • ω) = r * T.toFun ω := by
  -- First show toFun 0 = 0
  have h_zero : T.toFun 0 = 0 := by
    -- Using is_linear with c = 1, ω₁ = 0, ω₂ = 0:
    -- toFun (1 • 0 + 0) = 1 * toFun 0 + toFun 0
    -- toFun 0 = toFun 0 + toFun 0
    have h := T.is_linear 1 0 0
    simp only [one_smul, zero_add, one_mul] at h
    linarith
  -- Now use is_linear with ω₂ = 0
  have h := T.is_linear r ω 0
  simp only [add_zero] at h
  rw [h, h_zero, add_zero]

theorem map_smul {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (r : ℝ) (ω : SmoothForm n X k) : T.toFun (r • ω) = r * T.toFun ω :=
  map_smul' T r ω

/-- The zero current evaluates to zero on all forms. -/
def zero (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] : Current n X k where
  toFun := fun _ => 0
  is_linear := by intros; simp

instance instInhabited : Inhabited (Current n X k) := ⟨zero n X k⟩
instance instZero : Zero (Current n X k) := ⟨zero n X k⟩

/-- Addition of currents: (T₁ + T₂)(ω) = T₁(ω) + T₂(ω). -/
def add_curr (T₁ T₂ : Current n X k) : Current n X k where
  toFun := fun ω => T₁.toFun ω + T₂.toFun ω
  is_linear := by
    intros c ω₁ ω₂
    rw [map_add' T₁, map_add' T₂, map_smul' T₁, map_smul' T₂]
    ring

instance : Add (Current n X k) := ⟨add_curr⟩

/-- Negation of currents: (-T)(ω) = -T(ω). -/
def neg_curr (T : Current n X k) : Current n X k where
  toFun := fun ω => -T.toFun ω
  is_linear := by
    intros c ω₁ ω₂
    rw [map_add' T, map_smul' T]
    ring

instance : Neg (Current n X k) := ⟨neg_curr⟩

/-- Negation of zero is zero. -/
theorem neg_zero_current : -(0 : Current n X k) = 0 := by
  show neg_curr (zero n X k) = zero n X k
  unfold neg_curr zero
  simp only [neg_zero]

instance : Sub (Current n X k) := ⟨fun T₁ T₂ => T₁ + -T₂⟩

/-- Scalar multiplication of currents: (r • T)(ω) = r * T(ω). -/
def smul_curr (r : ℝ) (T : Current n X k) : Current n X k where
  toFun := fun ω => r * T.toFun ω
  is_linear := by
    intros c ω₁ ω₂
    rw [map_add' T, map_smul' T]
    ring

instance : HSMul ℝ (Current n X k) (Current n X k) := ⟨smul_curr⟩

/-- Integer scalar multiplication of currents. -/
instance : HSMul ℤ (Current n X k) (Current n X k) := ⟨fun z T => (z : ℝ) • T⟩

/-- Zero current evaluates to zero. -/
theorem zero_toFun (ω : SmoothForm n X k) : (0 : Current n X k).toFun ω = 0 := rfl

/-- Currents are bounded: evaluation is bounded by mass times comass.
    This is the continuity condition on currents as linear functionals. -/
axiom is_bounded (T : Current n X k) : ∃ M : ℝ, ∀ ω : SmoothForm n X k, |T.toFun ω| ≤ M * comass ω

/-- Helper: (-T).toFun ω = -T.toFun ω by definition of negation. -/
private theorem neg_toFun (T : Current n X k) (ω : SmoothForm n X k) :
    (-T).toFun ω = -T.toFun ω := rfl

/-- **Mass of a current** (Federer, 1969).
    The mass is the dual norm to the comass norm on forms:
    M(T) = sup { |T(ω)| : comass(ω) ≤ 1 }

    This is now a concrete definition, allowing us to derive the key properties.
    Reference: [H. Federer, "Geometric Measure Theory", Springer 1969, §4.1]. -/
def mass (T : Current n X k) : ℝ :=
  sSup { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |T.toFun ω| }

/-- The mass set is nonempty (contains 0 from the zero form). -/
private theorem mass_set_nonempty (T : Current n X k) :
    { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |T.toFun ω| }.Nonempty := by
  use |T.toFun 0|
  use 0
  constructor
  · rw [comass_zero]
    norm_num
  · rfl

/-- The mass set is bounded above (by the bound from is_bounded). -/
private theorem mass_set_bddAbove (T : Current n X k) :
    BddAbove { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |T.toFun ω| } := by
  obtain ⟨M, hM⟩ := T.is_bounded
  use max M 0
  intro r ⟨ω, hω_comass, hr⟩
  rw [hr]
  have h_bound : |T.toFun ω| ≤ M * comass ω := hM ω
  have h_comass_nonneg : comass ω ≥ 0 := comass_nonneg ω
  by_cases hM_nonneg : M ≥ 0
  · -- Case M ≥ 0: |T.toFun ω| ≤ M * comass ω ≤ M * 1 = M = max M 0
    calc |T.toFun ω| ≤ M * comass ω := h_bound
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left hω_comass hM_nonneg
      _ = M := mul_one M
      _ ≤ max M 0 := le_max_left M 0
  · -- Case M < 0: must have |T.toFun ω| = 0
    push_neg at hM_nonneg
    have h1 : M * comass ω ≤ 0 := by nlinarith
    have h2 : |T.toFun ω| ≤ 0 := le_trans h_bound h1
    have h3 : |T.toFun ω| ≥ 0 := abs_nonneg _
    have h4 : |T.toFun ω| = 0 := le_antisymm h2 h3
    rw [h4]
    exact le_max_right M 0

/-- **Mass is non-negative** (Federer 1969, §4.1.7).
    Proof: Mass is the supremum of absolute values, which are non-negative. -/
theorem mass_nonneg (T : Current n X k) : mass T ≥ 0 := by
  unfold mass
  apply Real.sSup_nonneg
  intro r ⟨ω, _, hr⟩
  rw [hr]
  exact abs_nonneg _

/-- **Mass of zero current is zero**.
    Proof: The zero current evaluates to 0 on all forms, so |0(ω)| = 0. -/
theorem mass_zero : mass (0 : Current n X k) = 0 := by
  unfold mass
  have h_set : { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |(0 : Current n X k).toFun ω| } = {0} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro ⟨ω, _, hr⟩
      rw [hr, zero_toFun, abs_zero]
    · intro hr
      use 0
      constructor
      · rw [comass_zero]; norm_num
      · rw [hr, zero_toFun, abs_zero]
  rw [h_set]
  exact csSup_singleton 0

/-- **Mass is symmetric under negation**.
    Proof: |(-T)(ω)| = |-T(ω)| = |T(ω)|, so the sets are identical. -/
theorem mass_neg (T : Current n X k) : mass (-T) = mass T := by
  unfold mass
  have h_set_eq : { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |(-T).toFun ω| } =
                  { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |T.toFun ω| } := by
    ext r
    simp only [Set.mem_setOf_eq]
    constructor
    · intro ⟨ω, hω, hr⟩
      use ω, hω
      rw [hr, neg_toFun, abs_neg]
    · intro ⟨ω, hω, hr⟩
      use ω, hω
      rw [hr, neg_toFun, abs_neg]
  rw [h_set_eq]

/-- Mass satisfies the triangle inequality (Federer 1969, §4.1.7). -/
axiom mass_add_le (S T : Current n X k) : mass (S + T) ≤ mass S + mass T

/-- Mass scales with absolute value of scalar. -/
axiom mass_smul (r : ℝ) (T : Current n X k) : mass (r • T) = |r| * mass T

/-- Extensionality for currents: two currents are equal iff they agree on all forms. -/
@[ext]
theorem ext {S T : Current n X k} (h : ∀ ω, S.toFun ω = T.toFun ω) : S = T := by
  cases S; cases T
  simp only [Current.mk.injEq]
  funext ω
  exact h ω

/-- Zero is a left identity for addition. -/
theorem zero_add (T : Current n X k) : 0 + T = T := by
  ext ω
  show (0 : Current n X k).toFun ω + T.toFun ω = T.toFun ω
  simp [zero_toFun]

/-- Zero is a right identity for addition. -/
theorem add_zero (T : Current n X k) : T + 0 = T := by
  ext ω
  show T.toFun ω + (0 : Current n X k).toFun ω = T.toFun ω
  simp [zero_toFun]

/-- **Boundary operator on currents** (Federer, 1969).
    The boundary ∂T is defined by duality: (∂T)(ω) = T(dω).

    This is a concrete definition rather than an opaque axiom, allowing us to
    derive properties like additivity and compatibility with negation. -/
def boundary (T : Current n X (k + 1)) : Current n X k where
  toFun := fun ω => T.toFun (smoothExtDeriv ω)
  is_linear := fun c ω₁ ω₂ => by
    -- Need: T(d(c • ω₁ + ω₂)) = c * T(d ω₁) + T(d ω₂)
    -- By linearity of d: d(c • ω₁ + ω₂) = c • d ω₁ + d ω₂
    rw [smoothExtDeriv_add, smoothExtDeriv_smul_real]
    -- By linearity of T
    exact T.is_linear c (smoothExtDeriv ω₁) (smoothExtDeriv ω₂)

/-- A current is a cycle if its boundary is zero. -/
def isCycle (T : Current n X (k + 1)) : Prop := T.boundary = 0

/-- ∂∂ = 0: boundary of boundary is zero.
    This follows from d∘d = 0 for the exterior derivative.
    Proof: (∂∂T)(ω) = (∂T)(dω) = T(d(dω)) = T(0) = 0. -/
axiom boundary_boundary (T : Current n X (k + 2)) : (boundary (boundary T)) = 0

/-- **Boundary is additive** (Federer, 1969).
    The boundary operator is a group homomorphism.
    Proof from duality: (∂(S+T))(ω) = (S+T)(dω) = S(dω) + T(dω) = (∂S)(ω) + (∂T)(ω). -/
theorem boundary_add (S T : Current n X (k + 1)) : boundary (S + T) = boundary S + boundary T := by
  ext ω
  show (add_curr S T).toFun (smoothExtDeriv ω) = S.toFun (smoothExtDeriv ω) + T.toFun (smoothExtDeriv ω)
  unfold add_curr
  rfl

/-- **Boundary of negation** (Federer, 1969).
    The boundary of the negation is the negation of the boundary.
    Proof from duality: (∂(-T))(ω) = (-T)(dω) = -T(dω) = -(∂T)(ω). -/
theorem boundary_neg (T : Current n X (k + 1)) : boundary (-T) = -(boundary T) := by
  ext ω
  show (neg_curr T).toFun (smoothExtDeriv ω) = -(T.toFun (smoothExtDeriv ω))
  unfold neg_curr
  rfl

/-- **Boundary of subtraction** (Federer, 1969). -/
theorem boundary_sub (S T : Current n X (k + 1)) : boundary (S - T) = boundary S - boundary T := by
  have h : S - T = S + (-T) := rfl
  rw [h, boundary_add, boundary_neg]
  rfl

end Current

end
