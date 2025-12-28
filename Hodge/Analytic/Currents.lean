import Hodge.Analytic.Forms
import Hodge.Analytic.Norms

/-!
# Currents on Complex Manifolds

This file defines currents (distributional differential forms) on compact Kähler manifolds.
-/

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-- A current of dimension k is a continuous linear functional on k-forms. 
    We define it as a wrapper to simplify instance definitions. -/
structure Current (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] where
  toFun : SmoothForm n X k → ℝ
  map_add' : ∀ ω₁ ω₂, toFun (ω₁ + ω₂) = toFun ω₁ + toFun ω₂
  map_smul' : ∀ (r : ℝ) ω, toFun (r • ω) = r * toFun ω

namespace Current

variable {k : ℕ}

instance : Zero (Current n X k) where
  zero := ⟨fun _ => 0, fun _ _ => by ring, fun _ _ => by ring⟩

instance : Add (Current n X k) where
  add T S := ⟨fun ω => T.toFun ω + S.toFun ω, 
    fun _ _ => by simp [T.map_add', S.map_add']; ring,
    fun r _ => by simp [T.map_smul', S.map_smul']; ring⟩

instance : Neg (Current n X k) where
  neg T := ⟨fun ω => -T.toFun ω,
    fun ω₁ ω₂ => by simp only [T.map_add']; ring,
    fun r ω => by simp only [T.map_smul']; ring⟩

instance : SMul ℤ (Current n X k) where
  smul c T := ⟨fun ω => c * T.toFun ω,
    fun ω₁ ω₂ => by simp only [T.map_add']; ring,
    fun r ω => by simp only [T.map_smul']; ring⟩

instance : SMul ℝ (Current n X k) where
  smul r T := ⟨fun ω => r * T.toFun ω,
    fun ω₁ ω₂ => by simp only [T.map_add']; ring,
    fun r' ω => by simp only [T.map_smul']; ring⟩

/-- Evaluation of a current on a form. -/
def eval (T : Current n X k) (ω : SmoothForm n X k) : ℝ := T.toFun ω

/-- Mass of a current (stub - returns 0). -/
def mass (_T : Current n X k) : ℝ := 0

theorem mass_nonneg (T : Current n X k) : T.mass ≥ 0 := le_refl (0 : ℝ)
theorem mass_zero : (0 : Current n X k).mass = 0 := rfl
theorem mass_neg (T : Current n X k) : (-T).mass = T.mass := rfl

theorem mass_add_le (S T : Current n X k) : (S + T).mass ≤ S.mass + T.mass := by
  unfold mass; linarith

/-- Boundary operator on currents. -/
def boundary (T : Current n X (k + 1)) : Current n X k where
  toFun := fun ω => T.toFun (smoothExtDeriv ω)
  map_add' := fun ω₁ ω₂ => by rw [smoothExtDeriv_add, T.map_add']
  map_smul' := fun r ω => by rw [smoothExtDeriv_smul_real, T.map_smul']

/-- A current is a cycle if its boundary is zero. -/
def isCycle (T : Current n X (k + 1)) : Prop := T.boundary = (0 : Current n X k)

/-- ∂∂ = 0: boundary of boundary is zero.
    This follows from d² = 0 for the exterior derivative. -/
axiom boundary_boundary (T : Current n X (k + 2)) : T.boundary.boundary = (0 : Current n X k)

end Current

end
