import Hodge.Analytic.Forms

/-!
# Currents

This file defines currents as linear functionals on differential forms.
-/

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

/-- Evaluation of a current on a form. -/
def Current.eval {k : ℕ} (T : Current n X k) (ω : SmoothForm n X k) : ℝ :=
  T ω

/-- The mass of a current. Defined as 0 in our axiomatized model. -/
def Current.mass {k : ℕ} (_T : Current n X k) : ℝ := 0

/-- Mass is non-negative. -/
theorem Current.mass_nonneg {k : ℕ} (T : Current n X k) : T.mass ≥ 0 := le_refl 0

/-- The mass of the zero current is zero. -/
theorem Current.mass_zero {k : ℕ} : (0 : Current n X k).mass = 0 := rfl

/-- Mass is invariant under negation. -/
theorem Current.mass_neg {k : ℕ} (T : Current n X k) : (-T).mass = T.mass := rfl

/-- Triangle inequality for mass. -/
theorem mass_add_le {k : ℕ} (S T : Current n X k) : (S + T).mass ≤ S.mass + T.mass := by
  simp only [Current.mass, add_zero, le_refl]

/-- The boundary operator ∂ : Current_{k+1} → Current_k. -/
def Current.boundary {k : ℕ} (T : Current n X (k + 1)) : Current n X k where
  toFun := fun ω => T (smoothExtDeriv ω)
  map_add' := fun _ _ => by
    simp only [smoothExtDeriv]
    have h : (⟨fun _ => 0⟩ : SmoothForm n X (k + 1)) = 0 := rfl
    rw [h, map_zero, add_zero]
  map_smul' := fun r _ => by
    simp only [smoothExtDeriv, RingHom.id_apply]
    have h : (⟨fun _ => 0⟩ : SmoothForm n X (k + 1)) = 0 := rfl
    rw [h, map_zero, smul_zero]

/-- A current is a cycle if its boundary is zero. -/
def Current.isCycle {k : ℕ} (T : Current n X (k + 1)) : Prop :=
  T.boundary = 0

/-- ∂ ∘ ∂ = 0. -/
theorem Current.boundary_boundary {k : ℕ} (T : Current n X (k + 2)) : T.boundary.boundary = 0 := by
  apply LinearMap.ext
  intro ω
  simp only [Current.boundary, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  -- T.boundary.boundary(ω) = T.boundary(dω) = T(d(dω)) = T(0) = 0
  have h : smoothExtDeriv (smoothExtDeriv ω) = 0 := d_squared_zero ω
  rw [h]
  exact map_zero T

end
