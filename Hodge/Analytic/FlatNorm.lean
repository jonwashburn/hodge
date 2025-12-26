/-!
# Track B.5: Flat Norm

This file defines the flat norm on currents and proves its basic properties.
The flat norm is the natural metric for the space of integral currents.

## Contents
- Flat norm definition
- Triangle inequality
- Relationship with mass norm
- Interface with compactness theorems

## Status
- [x] Define flat norm
- [x] Prove flat norm is non-negative
- [x] State triangle inequality (Axiom)
- [x] Prove flatNorm T ≤ mass T
-/

import Hodge.Analytic.Currents

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [ProjectiveComplexManifold n X] [KahlerStructure n X]

/-- The flat norm of a current T.
Defined as the infimum of mass(T - ∂Q) + mass(Q) over all (k+1)-currents Q. -/
def flatNorm {k : ℕ} (T : Current n X k) : ℝ :=
  sInf { r : ℝ | ∃ (Q : Current n X (k + 1)), r = (T - Q.boundary).mass + Q.mass }

/-- The flat norm is non-negative. -/
theorem flatNorm_nonneg {k : ℕ} (T : Current n X k) :
    flatNorm T ≥ 0 := by
  unfold flatNorm
  apply Real.sInf_nonneg
  rintro r ⟨Q, h_val⟩
  rw [h_val]
  apply add_nonneg
  · apply Current.mass_nonneg
  · apply Current.mass_nonneg

/-- The flat norm is bounded above by the mass.
(Choose Q = 0) -/
theorem flatNorm_le_mass {k : ℕ} (T : Current n X k) :
    flatNorm T ≤ T.mass := by
  unfold flatNorm
  apply Real.sInf_le
  · -- The set is bounded below (by 0)
    use 0
    rintro r ⟨Q, h_val⟩
    rw [h_val]
    apply add_nonneg (Current.mass_nonneg _) (Current.mass_nonneg _)
  · use 0
    simp only [Current.boundary, LinearMap.coe_mk, AddHom.coe_mk, extDeriv,
      LinearMap.map_zero, sub_zero, add_zero, Current.mass_zero]
    -- Since ∂0 = 0 and mass(0) = 0, (T-0).mass + mass(0) = T.mass
    -- We need ∂0 = 0
    have : (0 : Current n X (k+1)).boundary = 0 := by
      ext ω; unfold Current.boundary; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
    rw [this, sub_zero, Current.mass_zero, add_zero]

/-- The flat norm satisfies the triangle inequality. -/
theorem flatNorm_add_le {k : ℕ} (S T : Current n X k) :
    flatNorm (S + T) ≤ flatNorm S + flatNorm T := by
  -- Proof:
  -- 1. For any Q₁, Q₂, let r₁ = (S - ∂Q₁).mass + Q₁.mass and r₂ = (T - ∂Q₂).mass + Q₂.mass.
  -- 2. Then r₁ + r₂ = (S - ∂Q₁).mass + (T - ∂Q₂).mass + Q₁.mass + Q₂.mass
  -- 3. By triangle inequality for mass:
  --    (S - ∂Q₁).mass + (T - ∂Q₂).mass ≥ ((S + T) - ∂(Q₁ + Q₂)).mass
  -- 4. By triangle inequality for mass:
  --    Q₁.mass + Q₂.mass ≥ (Q₁ + Q₂).mass
  -- 5. So r₁ + r₂ ≥ ((S + T) - ∂(Q₁ + Q₂)).mass + (Q₁ + Q₂).mass
  -- 6. This shows flatNorm (S + T) ≤ r₁ + r₂ for all r₁, r₂.
  unfold flatNorm
  apply Real.le_sInf_add_sInf
  · -- set for S is not empty
    use S.mass; use 0; simp [Current.mass_zero, Current.boundary_boundary]
    -- wait, ∂0 = 0
    have : (0 : Current n X (k+1)).boundary = 0 := by
      ext ω; unfold Current.boundary; simp
    rw [this, sub_zero, Current.mass_zero, add_zero]
  · -- set for T is not empty
    use T.mass; use 0; have : (0 : Current n X (k+1)).boundary = 0 := by ext ω; unfold Current.boundary; simp
    rw [this, sub_zero, Current.mass_zero, add_zero]
  · -- set for S is bounded below
    use 0; rintro r ⟨Q, h⟩; rw [h]; exact add_nonneg (Current.mass_nonneg _) (Current.mass_nonneg _)
  · -- set for T is bounded below
    use 0; rintro r ⟨Q, h⟩; rw [h]; exact add_nonneg (Current.mass_nonneg _) (Current.mass_nonneg _)
  · rintro r₁ ⟨Q₁, rfl⟩ r₂ ⟨Q₂, rfl⟩
    use Q₁ + Q₂
    have h_bound : (Q₁ + Q₂).boundary = Q₁.boundary + Q₂.boundary := by
      ext ω; unfold Current.boundary; simp [d_add, map_add]
    rw [h_bound]
    calc ((S + T) - (Q₁.boundary + Q₂.boundary)).mass + (Q₁ + Q₂).mass
        = ((S - Q₁.boundary) + (T - Q₂.boundary)).mass + (Q₁ + Q₂).mass := by
          congr 1; abel
      _ ≤ (S - Q₁.boundary).mass + (T - Q₂.boundary).mass + (Q₁.mass + Q₂.mass) := by
          apply add_le_add
          · exact Current.mass_add_le _ _
          · exact Current.mass_add_le _ _
      _ = (S - Q₁.boundary).mass + Q₁.mass + ((T - Q₂.boundary).mass + Q₂.mass) := by
          ring

/-- Fundamental estimate: |T(ψ)| ≤ flatNorm(T) * max(comass(ψ), comass(dψ)).
This shows that flat norm convergence implies weak-* convergence. -/
theorem eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T ψ| ≤ flatNorm T * max (comass ψ) (comass (extDeriv ψ)) := by
  let C := max (comass ψ) (comass (extDeriv ψ))
  unfold flatNorm
  apply Real.le_sInf_mul_const
  · -- Non-empty
    use T.mass; use 0
    simp only [Current.boundary, LinearMap.coe_mk, AddHom.coe_mk, extDeriv,
      LinearMap.map_zero, sub_zero, add_zero, Current.mass_zero]
  · rintro r ⟨Q, h_val⟩
    rw [h_val]
    calc |T ψ| = |(T - Q.boundary) ψ + Q (extDeriv ψ)| := by
        simp only [LinearMap.sub_apply, LinearMap.add_apply, Current.boundary]
        abel
      _ ≤ |(T - Q.boundary) ψ| + |Q (extDeriv ψ)| := abs_add _ _
      _ ≤ (T - Q.boundary).mass * comass ψ + Q.mass * comass (extDeriv ψ) := by
        apply add_le_add
        · apply Current.eval_le_mass; exact le_refl _
        · apply Current.eval_le_mass; exact le_refl _
      _ ≤ (T - Q.boundary).mass * C + Q.mass * C := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left (le_max_left _ _) (Current.mass_nonneg _)
        · apply mul_le_mul_of_nonneg_left (le_max_right _ _) (Current.mass_nonneg _)
      _ = ((T - Q.boundary).mass + Q.mass) * C := by ring
  · apply add_nonneg (Current.mass_nonneg _) (Current.mass_nonneg _)


end
