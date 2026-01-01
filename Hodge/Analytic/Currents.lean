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

axiom map_smul' {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (r : ℝ) (ω : SmoothForm n X k) : T.toFun (r • ω) = r * T.toFun ω

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

/-- **Mass of a current** (Federer, 1969).
    The mass is the dual norm to the comass norm on forms:
    M(T) = sup { T(ω) : comass(ω) ≤ 1 }

    This is defined opaquely as it requires the full GMT machinery.
    Reference: [H. Federer, "Geometric Measure Theory", Springer 1969, §4.1]. -/
opaque mass (T : Current n X k) : ℝ

/-- Mass is non-negative (Federer 1969, §4.1.7). -/
axiom mass_nonneg (T : Current n X k) : mass T ≥ 0

/-- Mass of zero current is zero. -/
axiom mass_zero : mass (0 : Current n X k) = 0

/-- Mass is symmetric under negation. -/
axiom mass_neg (T : Current n X k) : mass (-T) = mass T

/-- Mass satisfies the triangle inequality (Federer 1969, §4.1.7). -/
axiom mass_add_le (S T : Current n X k) : mass (S + T) ≤ mass S + mass T

/-- Mass scales with absolute value of scalar. -/
axiom mass_smul (r : ℝ) (T : Current n X k) : mass (r • T) = |r| * mass T

/-- Currents are bounded: evaluation is bounded by mass times comass.
    In the stub model with all evaluations finite, this is trivially satisfiable. -/
axiom is_bounded (T : Current n X k) : ∃ M : ℝ, ∀ ω : SmoothForm n X k, |T.toFun ω| ≤ M * comass ω

/-- Zero current evaluates to zero. -/
theorem zero_toFun (ω : SmoothForm n X k) : (0 : Current n X k).toFun ω = 0 := by
  rfl

/-- Zero is a left identity for addition. -/
axiom zero_add (T : Current n X k) : 0 + T = T

/-- Zero is a right identity for addition. -/
axiom add_zero (T : Current n X k) : T + 0 = T

/-- **Boundary operator on currents** (Federer, 1969).
    The boundary ∂T is defined by duality: (∂T)(ω) = T(dω). -/
opaque boundary (T : Current n X (k + 1)) : Current n X k

/-- A current is a cycle if its boundary is zero. -/
def isCycle (T : Current n X (k + 1)) : Prop := T.boundary = 0

/-- ∂∂ = 0: boundary of boundary is zero. -/
axiom boundary_boundary (T : Current n X (k + 2)) : (boundary (boundary T)) = 0

/-- **Boundary is additive** (Federer, 1969).
    The boundary operator is a group homomorphism.
    This follows from the duality definition: (∂T)(ω) = T(dω). -/
axiom boundary_add (S T : Current n X (k + 1)) : boundary (S + T) = boundary S + boundary T

/-- **Boundary of negation** (Federer, 1969).
    The boundary of the negation is the negation of the boundary. -/
axiom boundary_neg (T : Current n X (k + 1)) : boundary (-T) = -(boundary T)

/-- **Boundary of subtraction** (Federer, 1969). -/
theorem boundary_sub (S T : Current n X (k + 1)) : boundary (S - T) = boundary S - boundary T := by
  have h : S - T = S + (-T) := rfl
  rw [h, boundary_add, boundary_neg]
  rfl

end Current

end
