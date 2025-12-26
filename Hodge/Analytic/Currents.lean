/-!
# Track B.3: Currents

This file defines currents as continuous linear functionals on differential forms,
with the mass norm and boundary operator.

## Contents
- Current type as linear functionals
- Mass norm (dual to comass)
- Boundary operator via duality with d
- Basic norm properties

## Status
- [x] Define Current type
- [x] Define mass
- [x] Prove mass_neg
- [ ] Prove mass_add_le (has sorry)
- [x] Define boundary
- [ ] Prove boundary ∘ boundary = 0
-/

import Hodge.Analytic.Norms

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [ProjectiveComplexManifold n X] [KahlerStructure n X]

/-! ## Current Type -/

/-- A current of dimension k is a continuous linear functional on k-forms.
This is the distributional dual to the space of smooth forms. -/
def Current (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
    [SmoothManifoldWithCorners 𝓒(Complex, n) X] :=
  SmoothForm n X k →ₗ[ℝ] ℝ

/-- Evaluation of a current on a form. -/
def Current.eval {k : ℕ} (T : Current n X k) (ω : SmoothForm n X k) : ℝ :=
  T ω

/-! ## Mass Norm -/

/-- The mass of a current: the dual norm to comass.
mass(T) = sup { |T(ω)| : comass(ω) ≤ 1 } -/
def Current.mass {k : ℕ} (T : Current n X k) : ℝ :=
  sSup { r : ℝ | ∃ (α : SmoothForm n X k), comass α ≤ 1 ∧ r = |T α| }

/-- Mass is non-negative. -/
theorem Current.mass_nonneg {k : ℕ} (T : Current n X k) :
    T.mass ≥ 0 := by
  unfold Current.mass
  apply Real.sSup_nonneg
  rintro r ⟨α, _, h_val⟩
  rw [h_val]
  apply abs_nonneg

/-- Mass is invariant under negation: mass(-T) = mass(T). -/
theorem Current.mass_neg {k : ℕ} (T : Current n X k) :
    (-T).mass = T.mass := by
  unfold Current.mass
  congr 1
  ext r
  constructor
  · rintro ⟨α, h_comass, h_val⟩
    use α, h_comass
    simp only [LinearMap.neg_apply, abs_neg] at h_val ⊢
    exact h_val
  · rintro ⟨α, h_comass, h_val⟩
    use α, h_comass
    simp only [LinearMap.neg_apply, abs_neg]
    exact h_val

/-- Triangle inequality for mass: mass(S + T) ≤ mass(S) + mass(T). -/
theorem Current.mass_add_le {k : ℕ}
    (S T : Current n X k) :
    (S + T).mass ≤ S.mass + T.mass := by
  unfold Current.mass
  apply Real.sSup_le
  · rintro r ⟨α, h_comass, h_val⟩
    rw [h_val, LinearMap.add_apply]
    calc |S α + T α| ≤ |S α| + |T α| := abs_add (S α) (T α)
      _ ≤ sSup {r | ∃ α, comass α ≤ 1 ∧ r = |S α|} +
          sSup {r | ∃ α, comass α ≤ 1 ∧ r = |T α|} := by
        apply add_le_add
        · apply Real.le_sSup
          · -- The set { |S α| : comass α ≤ 1 } is bounded above
            -- This is a standard property of continuous linear functionals
            -- on a space with a norm (comass).
            sorry
          · exact ⟨α, h_comass, rfl⟩
        · apply Real.le_sSup
          · sorry
          · exact ⟨α, h_comass, rfl⟩
  · -- Non-empty: use the zero form
    use 0
    constructor
    · -- comass(0) = 0 ≤ 1
      exact comass_nonneg 0
    · simp only [LinearMap.map_zero, abs_zero]

/-- The calibration inequality: |T(ψ)| ≤ mass(T) when comass(ψ) ≤ 1. -/
theorem Current.eval_le_mass {k : ℕ}
    (T : Current n X k) (ψ : SmoothForm n X k) (h : comass ψ ≤ 1) :
    |T ψ| ≤ T.mass := by
  unfold Current.mass
  apply Real.le_sSup
  · use |T ψ|
    exact ⟨ψ, h, rfl⟩
  · exact ⟨ψ, h, rfl⟩


/-! ## Boundary Operator -/

/-- The boundary operator ∂ : Current_{k+1} → Current_k.
Defined by duality: ∂T(ω) = T(dω). -/
def Current.boundary {k : ℕ} (T : Current n X (k + 1)) : Current n X k where
  toFun := fun ω => T (extDeriv ω)
  map_add' := fun ω₁ ω₂ => by
    simp only [d_add, map_add]
  map_smul' := fun r ω => by
    simp only [d_smul, RingHom.id_apply, LinearMap.map_smul]

/-- A current is a cycle if its boundary is zero. -/
def Current.isCycle {k : ℕ} (T : Current n X k) : Prop :=
  ∀ (ω : SmoothForm n X (k - 1)), T.boundary ω = 0

/-- ∂ ∘ ∂ = 0: the boundary of a boundary is zero.
This follows from d ∘ d = 0. -/
theorem Current.boundary_boundary {k : ℕ} (T : Current n X (k + 2)) :
    T.boundary.boundary = 0 := by
  ext ω
  unfold Current.boundary
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, d_squared_zero, map_zero]

end
