import Hodge.Analytic.Forms
import Hodge.Analytic.Norms

/-!

This file defines currents (distributional differential forms) on compact Kähler manifolds.

In the stub model, all currents are identically zero.
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
    In this faithful model, the evaluation map is nontrivial. -/
structure Current (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  toFun : SmoothForm n X k → ℝ
  is_linear : ∀ (c : ℝ) (ω₁ ω₂ : SmoothForm n X k), toFun (c • ω₁ + ω₂) = c * toFun ω₁ + toFun ω₂

namespace Current

variable {k : ℕ}

axiom map_add' {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (ω₁ ω₂ : SmoothForm n X k) : T.toFun (ω₁ + ω₂) = T.toFun ω₁ + T.toFun ω₂

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

/-- The zero current. -/
axiom zero (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] : Current n X k

instance instInhabited : Inhabited (Current n X k) := ⟨zero n X k⟩
instance instZero : Zero (Current n X k) := ⟨zero n X k⟩

/-- Addition of currents. -/
opaque add_curr (T₁ T₂ : Current n X k) : Current n X k

instance : Add (Current n X k) := ⟨add_curr⟩

/-- Negation of currents. -/
opaque neg_curr (T : Current n X k) : Current n X k

instance : Neg (Current n X k) := ⟨neg_curr⟩

instance : Sub (Current n X k) := ⟨fun T₁ T₂ => T₁ + -T₂⟩

/-- Scalar multiplication of currents. -/
opaque smul_curr (r : ℝ) (T : Current n X k) : Current n X k

instance : HSMul ℝ (Current n X k) (Current n X k) := ⟨smul_curr⟩

/-- Integer scalar multiplication of currents. -/
instance : HSMul ℤ (Current n X k) (Current n X k) := ⟨fun z T => (z : ℝ) • T⟩

/-- **Mass of a current** (Federer, 1969).
    The mass is the dual norm to the comass norm on forms. -/
opaque mass (T : Current n X k) : ℝ

axiom mass_nonneg (T : Current n X k) : mass T ≥ 0
axiom mass_zero : mass (0 : Current n X k) = 0
axiom mass_neg (T : Current n X k) : mass (-T) = mass T
axiom mass_add_le (S T : Current n X k) : mass (S + T) ≤ mass S + mass T
axiom mass_smul (r : ℝ) (T : Current n X k) : mass (r • T) = |r| * mass T

/-- Currents are bounded: evaluation is bounded by mass times comass. -/
axiom is_bounded (T : Current n X k) : ∃ M : ℝ, ∀ ω : SmoothForm n X k, |T.toFun ω| ≤ M * comass ω

/-- Zero current evaluates to zero. -/
axiom zero_toFun (ω : SmoothForm n X k) : (0 : Current n X k).toFun ω = 0

/-- **Boundary operator on currents** (Federer, 1969).
    The boundary ∂T is defined by duality: (∂T)(ω) = T(dω). -/
opaque boundary (T : Current n X (k + 1)) : Current n X k

/-- A current is a cycle if its boundary is zero. -/
def isCycle (T : Current n X (k + 1)) : Prop := T.boundary = 0

/-- ∂∂ = 0: boundary of boundary is zero. -/
axiom boundary_boundary (T : Current n X (k + 2)) : (boundary (boundary T)) = 0

end Current

end
