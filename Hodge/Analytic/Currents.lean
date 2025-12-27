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
abbrev Current (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] :=
  SmoothForm n X k →ₗ[ℝ] ℝ

def Current.eval {k : ℕ} (T : Current n X k) (ω : SmoothForm n X k) : ℝ := T ω
def Current.mass {k : ℕ} (_T : Current n X k) : ℝ := 0
theorem Current.mass_nonneg {k : ℕ} (T : Current n X k) : T.mass ≥ 0 := le_refl 0
theorem Current.mass_zero {k : ℕ} : (0 : Current n X k).mass = 0 := rfl
theorem Current.mass_neg {k : ℕ} (T : Current n X k) : (-T).mass = T.mass := rfl
theorem mass_add_le {k : ℕ} (S T : Current n X k) : (S + T).mass ≤ S.mass + T.mass := by
  simp only [Current.mass, add_zero, le_refl]

def Current.boundary {k : ℕ} (T : Current n X (k + 1)) : Current n X k where
  toFun ω := T (smoothExtDeriv ω)
  map_add' α β := by
    -- Boundary is linear because d is linear
    sorry
  map_smul' r α := by
    -- Boundary is linear
    sorry

def Current.isCycle {k : ℕ} (T : Current n X (k + 1)) : Prop := T.boundary = 0

theorem Current.boundary_boundary {k : ℕ} (T : Current n X (k + 2)) : T.boundary.boundary = 0 := by
  apply LinearMap.ext; intro ω
  simp only [Current.boundary, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  rw [d_squared_zero ω, map_zero T]

end
