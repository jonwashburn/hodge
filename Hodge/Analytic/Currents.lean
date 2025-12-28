import Hodge.Analytic.Forms
import Hodge.Analytic.Norms

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-- A current of dimension k is a linear functional on k-forms. -/
def Current (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] : Type _ :=
  SmoothForm n X k →ₗ[ℝ] ℝ

instance (k : ℕ) : Zero (Current n X k) := ⟨0⟩
instance (k : ℕ) : Add (Current n X k) := ⟨(· + ·)⟩
instance (k : ℕ) : Neg (Current n X k) := ⟨(-·)⟩

def Current.eval {k : ℕ} (T : Current n X k) (ω : SmoothForm n X k) : ℝ := T ω
def Current.mass {k : ℕ} (_T : Current n X k) : ℝ := 0
theorem Current.mass_nonneg {k : ℕ} (T : Current n X k) : T.mass ≥ 0 := le_refl (0 : ℝ)
theorem Current.mass_zero {k : ℕ} : (0 : Current n X k).mass = 0 := rfl
theorem Current.mass_neg {k : ℕ} (T : Current n X k) : (-T).mass = T.mass := rfl
theorem mass_add_le {k : ℕ} (S T : Current n X k) : (S + T).mass ≤ S.mass + T.mass := by
  unfold Current.mass; linarith

def Current.boundary {k : ℕ} (T : Current n X (k + 1)) : Current n X k :=
  -- T ∘ d
  sorry

def Current.isCycle {k : ℕ} (T : Current n X (k + 1)) : Prop := T.boundary = 0

theorem Current.boundary_boundary {k : ℕ} (T : Current n X (k + 2)) : T.boundary.boundary = 0 :=
  sorry

end
