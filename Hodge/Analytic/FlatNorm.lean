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
- [ ] Prove flat norm is non-negative
- [ ] Prove triangle inequality
- [ ] Prove flat_norm T ≤ mass T
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
      LinearMap.map_zero, sub_zero, add_zero]
    -- Need to show 0.mass = 0 and (boundary 0) = 0
    sorry

/-- The flat norm satisfies the triangle inequality. -/
theorem flatNorm_add_le {k : ℕ} (S T : Current n X k) :
    flatNorm (S + T) ≤ flatNorm S + flatNorm T := by
  -- Proof:
  -- flatNorm S = inf { mass(S - ∂Q₁) + mass(Q₁) }
  -- flatNorm T = inf { mass(T - ∂Q₂) + mass(Q₂) }
  -- For any ε > 0, choose Q₁, Q₂ such that:
  -- mass(S - ∂Q₁) + mass(Q₁) < flatNorm S + ε
  -- mass(T - ∂Q₂) + mass(Q₂) < flatNorm T + ε
  -- Then Q := Q₁ + Q₂ satisfies:
  -- mass((S + T) - ∂Q) + mass(Q) = mass((S - ∂Q₁) + (T - ∂Q₂)) + mass(Q₁ + Q₂)
  -- ≤ mass(S - ∂Q₁) + mass(T - ∂Q₂) + mass(Q₁) + mass(Q₂)
  -- < flatNorm S + flatNorm T + 2ε
  sorry

/-- Fundamental estimate: |T(ψ)| ≤ flat_norm(T) * max(comass(ψ), comass(dψ)).
This shows that flat norm convergence implies weak-* convergence. -/
theorem eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T ψ| ≤ flatNorm T * max (comass ψ) (comass (extDeriv ψ)) := by
  -- Proof:
  -- For any Q, T(ψ) = (T - ∂Q)(ψ) + Q(dψ)
  -- |T(ψ)| ≤ |(T - ∂Q)(ψ)| + |Q(dψ)|
  -- |T(ψ)| ≤ mass(T - ∂Q) * comass(ψ) + mass(Q) * comass(dψ)
  -- |T(ψ)| ≤ (mass(T - ∂Q) + mass(Q)) * max(comass(ψ), comass(dψ))
  -- Take infimum over Q.
  sorry

end
