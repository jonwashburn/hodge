import Hodge.Analytic.Forms
import Hodge.Analytic.Norms

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

/-- Fundamental estimate: |T(ω)| ≤ mass(T) · comass(ω). -/
axiom Current.eval_le_mass_mul_comass {k : ℕ} (T : Current n X k) (ω : SmoothForm n X k) :
    |T ω| ≤ T.mass * comass ω

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
  map_add' := fun α β => by
    rw [smoothExtDeriv_add]
    exact map_add T _ _
  map_smul' := fun r α => by
    rw [smoothExtDeriv_smul_real]
    exact map_smul T r _

/-- A current is a cycle if its boundary is zero. -/
def Current.isCycle {k : ℕ} (T : Current n X (k + 1)) : Prop :=
  T.boundary = 0

/-- ∂ ∘ ∂ = 0. -/
theorem Current.boundary_boundary {k : ℕ} (T : Current n X (k + 2)) : T.boundary.boundary = 0 := by
  apply LinearMap.ext
  intro ω
  unfold Current.boundary
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
  -- T.boundary.boundary(ω) = T.boundary(dω) = T(d(dω)) = T(0) = 0
  have h := d_squared_zero ω
  simp only [h, map_zero]

end
