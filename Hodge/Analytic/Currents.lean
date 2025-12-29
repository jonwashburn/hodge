import Hodge.Analytic.Forms
import Hodge.Analytic.Norms

/-!
# Currents on Complex Manifolds

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

/-- A current of dimension k is a continuous linear functional on k-forms.
    In the stub model, all currents are identically zero. -/
@[ext]
structure Current (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  toFun : SmoothForm n X k → ℝ
  toFun_zero : ∀ ψ, toFun ψ = 0

namespace Current

variable {k : ℕ}

theorem map_add {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (ω₁ ω₂ : SmoothForm n X k) : T.toFun (ω₁ + ω₂) = T.toFun ω₁ + T.toFun ω₂ := by
  rw [T.toFun_zero, T.toFun_zero, T.toFun_zero]; simp

theorem map_smul {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (r : ℝ) (ω : SmoothForm n X k) : T.toFun (r • ω) = r * T.toFun ω := by
  rw [T.toFun_zero, T.toFun_zero]; simp

/-- The zero current. -/
def zero : Current n X k := {
  toFun := fun _ => 0
  toFun_zero := fun _ => rfl
}

instance : Zero (Current n X k) := ⟨zero⟩

/-- Addition of currents. -/
instance : Add (Current n X k) where
  add _ _ := 0

/-- Negation of currents. -/
instance : Neg (Current n X k) where
  neg _ := 0

/-- Subtraction of currents. -/
instance : Sub (Current n X k) where
  sub _ _ := 0

/-- Integer scalar multiplication of currents. -/
instance : HSMul ℤ (Current n X k) (Current n X k) where
  hSMul _ _ := 0

/-- Real scalar multiplication of currents. -/
instance : HSMul ℝ (Current n X k) (Current n X k) where
  hSMul _ _ := 0

/-- Mass of a current (stub - returns 0). -/
def mass (_T : Current n X k) : ℝ := 0

theorem mass_nonneg (T : Current n X k) : T.mass ≥ 0 := le_refl 0
theorem mass_zero : (0 : Current n X k).mass = 0 := rfl
theorem mass_neg (T : Current n X k) : (-T).mass = T.mass := rfl

theorem mass_add_le (S T : Current n X k) : (S + T).mass ≤ S.mass + T.mass := by
  unfold mass; linarith

/-- Boundary operator on currents.
    In the stub model, the boundary of any current is zero. -/
def boundary (_T : Current n X (k + 1)) : Current n X k := 0

/-- A current is a cycle if its boundary is zero. -/
def isCycle (T : Current n X (k + 1)) : Prop := T.boundary = 0

/-- Helper lemma for zero current. -/
@[simp] lemma zero_toFun (ω : SmoothForm n X k) : (0 : Current n X k).toFun ω = 0 := by
  rw [(0 : Current n X k).toFun_zero]

/-- ∂∂ = 0: boundary of boundary is zero. -/
theorem boundary_boundary (_T : Current n X (k + 2)) : (boundary (boundary _T)) = 0 := rfl

end Current

end
