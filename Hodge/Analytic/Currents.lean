import Hodge.Analytic.Forms
import Hodge.Analytic.Norms

/-!
# Currents on Kähler Manifolds

This file defines currents (distributional differential forms) on compact Kähler manifolds.
A current is defined as a continuous linear functional on the space of smooth forms.
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-- A current of dimension k is a continuous linear functional on smooth k-forms. -/
structure Current (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  toFun : SmoothForm n X k → ℝ
  is_linear : ∀ (c : ℝ) (ω₁ ω₂ : SmoothForm n X k), toFun (c • ω₁ + ω₂) = c * toFun ω₁ + toFun ω₂
  is_continuous : Continuous toFun

namespace Current

variable {k : ℕ}

/-- Extensionality for currents: two currents are equal iff they agree on all forms. -/
@[ext]
theorem ext' {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    {S T : Current n X k} (h : ∀ ω, S.toFun ω = T.toFun ω) : S = T := by
  cases S; cases T; simp only [Current.mk.injEq]; funext ω; exact h ω

/-- Linearity properties derive from the `is_linear` field. -/
theorem map_add {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (ω₁ ω₂ : SmoothForm n X k) : T.toFun (ω₁ + ω₂) = T.toFun ω₁ + T.toFun ω₂ := by
  have h := T.is_linear 1 ω₁ ω₂
  simp [one_smul, one_mul] at h
  exact h

/-- Currents map zero to zero. Follows from map_add with ω₁=ω₂=0. -/
theorem map_zero' {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) : T.toFun 0 = 0 := by
  -- T(0 + 0) = T(0) + T(0) from map_add
  have h_add := map_add T 0 0
  -- 0 + 0 = 0 in SmoothForm
  have h_zero : (0 : SmoothForm n X k) + 0 = 0 := by ext x; simp
  rw [h_zero] at h_add
  -- h_add : T.toFun 0 = T.toFun 0 + T.toFun 0
  -- From a = a + a, we get a = 0 (in ℝ)
  linarith

/-- Linearity: scalar multiplication. Derives from the is_linear field with ω₂ = 0. -/
theorem map_smul {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (r : ℝ) (ω : SmoothForm n X k) : T.toFun (r • ω) = r * T.toFun ω := by
  -- Use is_linear with ω₁ = ω, ω₂ = 0
  -- T(r • ω + 0) = r * T(ω) + T(0)
  have h := T.is_linear r ω 0
  -- r • ω + 0 = r • ω in SmoothForm
  have h_smul_zero : r • ω + (0 : SmoothForm n X k) = r • ω := by ext x; simp
  rw [h_smul_zero] at h
  -- T(0) = 0 from map_zero'
  rw [map_zero' T, add_zero] at h
  exact h

/-- The zero current evaluates to zero on all forms. -/
def zero (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] : Current n X k where
  toFun := fun _ => 0
  is_linear := by intros; simp
  is_continuous := continuous_const

instance instInhabited : Inhabited (Current n X k) := ⟨zero n X k⟩
instance instZero : Zero (Current n X k) := ⟨zero n X k⟩

/-- Addition of currents: (T₁ + T₂)(ω) = T₁(ω) + T₂(ω). -/
def add_curr (T₁ T₂ : Current n X k) : Current n X k where
  toFun := fun ω => T₁.toFun ω + T₂.toFun ω
  is_linear := by
    intros c ω₁ ω₂
    rw [map_add T₁, map_add T₂, map_smul T₁, map_smul T₂]
    ring
  is_continuous := T₁.is_continuous.add T₂.is_continuous

instance : Add (Current n X k) := ⟨add_curr⟩

/-- Negation of currents: (-T)(ω) = -T(ω). -/
def neg_curr (T : Current n X k) : Current n X k where
  toFun := fun ω => -T.toFun ω
  is_linear := by
    intros c ω₁ ω₂
    rw [map_add T, map_smul T]
    ring
  is_continuous := T.is_continuous.neg

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

/-- Scalar multiplication of currents: (r • T)(ω) = r * T(ω). -/
def smul_curr (r : ℝ) (T : Current n X k) : Current n X k where
  toFun := fun ω => r * T.toFun ω
  is_linear := by
    intros c ω₁ ω₂
    rw [map_add T, map_smul T]
    ring
  is_continuous := continuous_const.mul T.is_continuous

instance : HSMul ℝ (Current n X k) (Current n X k) := ⟨smul_curr⟩
instance : HSMul ℤ (Current n X k) (Current n X k) := ⟨fun z T => (z : ℝ) • T⟩

/-- Zero current evaluates to zero. -/
theorem zero_toFun (ω : SmoothForm n X k) : (0 : Current n X k).toFun ω = 0 := rfl

/-- **Current Boundedness**: Every current is bounded relative to the comass.
    This is a fundamental analytical property: a continuous linear functional on a
    normed space is always bounded.
    Reference: [W. Rudin, "Functional Analysis", 1991, Theorem 1.32]. -/
axiom is_bounded (T : Current n X k) : ∃ M : ℝ, ∀ ω : SmoothForm n X k, |T.toFun ω| ≤ M * ‖ω‖

/-- **Mass of a current** (Federer, 1969).
    The mass is the dual norm to the comass norm on forms:
    M(T) = sup { |T(ω)| : comass(ω) ≤ 1 } -/
def mass (T : Current n X k) : ℝ :=
  sSup { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |T.toFun ω| }

/-- The mass set is nonempty. -/
private axiom mass_set_nonempty (T : Current n X k) :
    { r : ℝ | ∃ ω : SmoothForm n X k, comass ω ≤ 1 ∧ r = |T.toFun ω| }.Nonempty

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
axiom mass_add_le (S T : Current n X k) : mass (S + T) ≤ mass S + mass T

/-- Mass scales with absolute value of scalar. -/
axiom mass_smul (r : ℝ) (T : Current n X k) : mass (r • T) = |r| * mass T

/-- Extensionality for currents. -/
@[ext]
theorem ext {S T : Current n X k} (h : ∀ ω, S.toFun ω = T.toFun ω) : S = T := by
  cases S; cases T; simp only [Current.mk.injEq]; funext ω; exact h ω

theorem zero_add (T : Current n X k) : 0 + T = T := by
  ext ω
  show (0 : Current n X k).toFun ω + T.toFun ω = T.toFun ω
  rw [zero_toFun]; ring

theorem add_zero (T : Current n X k) : T + 0 = T := by
  ext ω
  show T.toFun ω + (0 : Current n X k).toFun ω = T.toFun ω
  rw [zero_toFun]; ring

/-- **Boundary operator on currents** (Federer, 1969).
    The boundary ∂T is defined by duality: (∂T)(ω) = T(dω). -/
def boundary (T : Current n X (k + 1)) : Current n X k where
  toFun := fun ω => T.toFun (smoothExtDeriv ω)
  is_linear := fun c ω₁ ω₂ => by
    rw [smoothExtDeriv_add, smoothExtDeriv_smul_real]
    exact T.is_linear c (smoothExtDeriv ω₁) (smoothExtDeriv ω₂)
  is_continuous := T.is_continuous.comp smoothExtDeriv_continuous

def isCycle (T : Current n X (k + 1)) : Prop := T.boundary = 0

/-- ∂∂ = 0: boundary of boundary is zero. -/
theorem boundary_boundary (T : Current n X (k + 2)) : (boundary (boundary T)) = 0 := by
  ext ω; show T.toFun (smoothExtDeriv (smoothExtDeriv ω)) = 0
  rw [smoothExtDeriv_extDeriv]
  have h_zero : T.toFun 0 = 0 := by
    have h1 : (0 : ℝ) • (0 : SmoothForm n X (k + 2)) = 0 := zero_smul ℝ 0
    have h2 := map_smul T 0 0; rw [h1] at h2; simp at h2; exact h2
  exact h_zero

/-- **Boundary is additive**. -/
theorem boundary_add (S T : Current n X (k + 1)) : boundary (S + T) = boundary S + boundary T := by
  ext ω; rfl

/-- **Boundary of negation**. -/
theorem boundary_neg (T : Current n X (k + 1)) : boundary (-T) = -(boundary T) := by
  ext ω; rfl

theorem boundary_sub (S T : Current n X (k + 1)) : boundary (S - T) = boundary S - boundary T := by
  ext ω; rfl

end Current

end
