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
- [x] Prove mass_add_le
- [x] Define boundary
- [x] Prove boundary ∘ boundary = 0
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
    [ProjectiveComplexManifold n X] [KahlerStructure n X] :=
  SmoothForm n X k →L[ℝ] ℝ

/-- Evaluation of a current on a form. -/
def Current.eval {k : ℕ} (T : Current n X k) (ω : SmoothForm n X k) : ℝ :=
  T ω

/-! ## Mass Norm -/

/-- The mass of a current: the operator norm in the continuous dual.
mass(T) = sup { |T(ω)| : comass(ω) ≤ 1 } -/
def Current.mass {k : ℕ} (T : Current n X k) : ℝ :=
  ‖T‖

/-- **Theorem: Continuity of Currents**
Every current T has bounded evaluations on forms with comass ≤ 1.
Proof: This is the definition of the operator norm for continuous linear maps. -/
theorem mass_finite {k : ℕ} (T : Current n X k) :
    ∃ M : ℝ, ∀ α : SmoothForm n X k, comass α ≤ 1 → |T α| ≤ M := by
  use ‖T‖
  intro α hα
  exact T.le_opNorm α

/-- Mass is non-negative. -/
theorem Current.mass_nonneg {k : ℕ} (T : Current n X k) :
    T.mass ≥ 0 :=
  norm_nonneg T

/-- The mass of the zero current is zero. -/
theorem Current.mass_zero : (0 : Current n X k).mass = 0 :=
  norm_zero

/-- Mass is invariant under negation: mass(-T) = mass(T). -/
theorem Current.mass_neg {k : ℕ} (T : Current n X k) :
    (-T).mass = T.mass :=
  norm_neg T

/-- Triangle inequality for mass: mass(S + T) ≤ mass(S) + mass(T).
Proof: Mass is defined as the operator norm in the dual space. -/
theorem mass_add_le {k : ℕ}
    (S T : Current n X k) :
    (S + T).mass ≤ S.mass + T.mass :=
  norm_add_le S T

/-- The calibration inequality: |T(ψ)| ≤ mass(T) when comass(ψ) ≤ 1.
Proof: This is the definition of the operator norm for continuous linear maps. -/
theorem eval_le_mass {k : ℕ}
    (T : Current n X k) (ψ : SmoothForm n X k) (h : comass ψ ≤ 1) :
    |T ψ| ≤ T.mass :=
  T.le_opNorm ψ


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
