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
def Current (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] :=
  SmoothForm n X k →ₗ[ℝ] ℝ

/-- Evaluation of a current on a form. -/
def Current.eval {k : ℕ} (T : Current n X k) (ω : SmoothForm n X k) : ℝ :=
  T ω

/-- The mass of a current. Axiomatized. -/
def Current.mass {k : ℕ} (T : Current n X k) : ℝ := sorry

/-- Mass is non-negative. -/
theorem Current.mass_nonneg {k : ℕ} (T : Current n X k) : T.mass ≥ 0 := sorry

/-- The mass of the zero current is zero. -/
theorem Current.mass_zero : (0 : Current n X k).mass = 0 := sorry

/-- Mass is invariant under negation. -/
theorem Current.mass_neg {k : ℕ} (T : Current n X k) : (-T).mass = T.mass := sorry

/-- Triangle inequality for mass. -/
theorem mass_add_le {k : ℕ} (S T : Current n X k) : (S + T).mass ≤ S.mass + T.mass := sorry

/-- The boundary operator ∂ : Current_{k+1} → Current_k. -/
def Current.boundary {k : ℕ} (T : Current n X (k + 1)) : Current n X k where
  toFun := fun ω => T (extDeriv ω)
  map_add' := fun ω₁ ω₂ => by sorry
  map_smul' := fun r ω => by sorry

/-- A current is a cycle if its boundary is zero. -/
def Current.isCycle {k : ℕ} (T : Current n X k) : Prop :=
  ∀ (ω : SmoothForm n X (k - 1)), T.boundary ω = 0

/-- ∂ ∘ ∂ = 0. -/
theorem Current.boundary_boundary {k : ℕ} (T : Current n X (k + 2)) : T.boundary.boundary = 0 := sorry

end
