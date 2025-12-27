import Hodge.Analytic.Forms

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

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-! ## Current Type -/

/-- A current of dimension k is a continuous linear functional on k-forms.
This is the distributional dual to the space of smooth forms. -/
def Current (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] :=
  SmoothForm n X k →L[ℝ] ℝ

/-- Evaluation of a current on a form. -/
def Current.eval {k : ℕ} (T : Current n X k) (ω : SmoothForm n X k) : ℝ :=
  T ω

/-! ## Mass Norm -/

/-- The mass of a current: the operator norm in the continuous dual.
mass(T) = sup { |T(ω)| : comass(ω) ≤ 1 } -/
def Current.mass {k : ℕ} (T : Current n X k) : ℝ :=
  ‖T‖

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

/-! ## Boundary Operator -/

/-- The boundary operator ∂ : Current_{k+1} → Current_k.
Defined by duality: ∂T(ω) = T(dω). -/
def Current.boundary {k : ℕ} (T : Current n X (k + 1)) : Current n X k where
  toFun := fun ω => T (extDeriv ω)
  map_add' := fun ω₁ ω₂ => by
    -- extDeriv is linear, so extDeriv (ω₁ + ω₂) = extDeriv ω₁ + extDeriv ω₂
    have h_linear : extDeriv (ω₁ + ω₂) = extDeriv ω₁ + extDeriv ω₂ := by
      ext x v; simp only [extDeriv, Add.add, SmoothForm.as_alternating]
      -- extDerivAt is linear in the form
      rfl
    simp only [h_linear, map_add]
  map_smul' := fun r ω => by
    -- extDeriv commutes with scalar multiplication
    have h_smul : extDeriv (r • ω) = r • extDeriv ω := by
      ext x v; simp only [extDeriv, HSMul.hSMul, SMul.smul, SmoothForm.as_alternating]
      rfl
    simp only [h_smul, map_smul, RingHom.id_apply]

/-- A current is a cycle if its boundary is zero. -/
def Current.isCycle {k : ℕ} (T : Current n X k) : Prop :=
  ∀ (ω : SmoothForm n X (k - 1)), T.boundary ω = 0

/-- ∂ ∘ ∂ = 0: the boundary of a boundary is zero.
This follows from d ∘ d = 0. -/
theorem Current.boundary_boundary {k : ℕ} (T : Current n X (k + 2)) :
    T.boundary.boundary = 0 := by
  ext ω
  unfold Current.boundary
  simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.zero_apply]
  -- T.boundary.boundary(ω) = T.boundary(dω) = T(d(dω)) = T(0) = 0
  have h_dd : extDeriv (extDeriv ω) = 0 := d_squared_zero ω
  simp only [h_dd, map_zero]

end
