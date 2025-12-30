import Hodge.Analytic.Forms
import Hodge.Analytic.Norms

/-!
# Currents on Complex Manifolds

This file defines currents (distributional differential forms) on compact Kähler manifolds.

In the stub model, all currents are identically zero.
-/

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-- A current of dimension k is a continuous linear functional on smooth k-forms.
    In this faithful model, the evaluation map is nontrivial. -/
@[ext]
structure Current (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  toFun : SmoothForm n X k → ℝ
  is_linear : ∀ (c : ℝ) (ω₁ ω₂ : SmoothForm n X k), toFun (c • ω₁ + ω₂) = c * toFun ω₁ + toFun ω₂

namespace Current

variable {k : ℕ}

theorem map_add {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (ω₁ ω₂ : SmoothForm n X k) : T.toFun (ω₁ + ω₂) = T.toFun ω₁ + T.toFun ω₂ := by
  have h := T.is_linear 1 ω₁ ω₂
  simp at h; exact h

theorem map_smul {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : Current n X k) (r : ℝ) (ω : SmoothForm n X k) : T.toFun (r • ω) = r * T.toFun ω := by
  -- First note that `T(0)=0` from linearity.
  have h0' := T.is_linear 1 (0 : SmoothForm n X k) 0
  -- `T(0) = 1*T(0) + T(0)` hence `T(0)=0`
  have h0 : T.toFun (0 : SmoothForm n X k) = 0 := by
    have ha : T.toFun (0 : SmoothForm n X k) = T.toFun (0 : SmoothForm n X k) + T.toFun (0 : SmoothForm n X k) := by
      simpa using h0'
    have ha' : T.toFun (0 : SmoothForm n X k) + 0 =
        T.toFun (0 : SmoothForm n X k) + T.toFun (0 : SmoothForm n X k) := by
      simpa [add_zero] using ha
    have : 0 = T.toFun (0 : SmoothForm n X k) := add_left_cancel ha'
    simpa using this.symm
  have h := T.is_linear r ω 0
  -- simplify the linearity equation using `h0`
  have h' : T.toFun (r • ω) = r * T.toFun ω + T.toFun (0 : SmoothForm n X k) := by
    -- `r•ω + 0 = r•ω`
    simpa [add_zero] using h
  simpa [h0] using h'

/-- The zero current. -/
def zero : Current n X k := {
  toFun := fun _ => 0
  is_linear := fun _ _ _ => by simp
}

instance : Zero (Current n X k) := ⟨zero⟩

/-- Addition of currents. -/
def add_curr (T₁ T₂ : Current n X k) : Current n X k := {
  toFun := fun ω => T₁.toFun ω + T₂.toFun ω
  is_linear := fun c ω₁ ω₂ => by
    simp [T₁.is_linear, T₂.is_linear]
    ring
}

instance : Add (Current n X k) := ⟨add_curr⟩

/-- Negation of currents. -/
def neg_curr (T : Current n X k) : Current n X k := {
  toFun := fun ω => -T.toFun ω
  is_linear := fun c ω₁ ω₂ => by
    simp [T.is_linear]
    ring
}

instance : Neg (Current n X k) := ⟨neg_curr⟩

instance : Sub (Current n X k) := ⟨fun T₁ T₂ => T₁ + -T₂⟩

/-- Scalar multiplication of currents. -/
def smul_curr (r : ℝ) (T : Current n X k) : Current n X k := {
  toFun := fun ω => r * T.toFun ω
  is_linear := fun c ω₁ ω₂ => by
    simp [T.is_linear]
    ring
}

instance : HSMul ℝ (Current n X k) (Current n X k) := ⟨smul_curr⟩

/-- Integer scalar multiplication of currents. -/
instance : HSMul ℤ (Current n X k) (Current n X k) := ⟨fun z T => (z : ℝ) • T⟩

/-- **Mass of a current** (Federer, 1969).
    The mass is the dual norm to the comass norm on forms. -/
opaque mass (T : Current n X k) : ℝ

axiom mass_nonneg (T : Current n X k) : mass T ≥ 0
axiom mass_zero : mass (0 : Current n X k) = 0
axiom mass_neg (T : Current n X k) : mass (-T) = mass T
axiom mass_add_le (S T : Current n X k) : mass (S + T) ≤ mass S + mass T

/-- **Boundary operator on currents** (Federer, 1969).
    The boundary ∂T is defined by duality: (∂T)(ω) = T(dω). -/
def boundary (T : Current n X (k + 1)) : Current n X k := {
  toFun := fun ω => T.toFun (smoothExtDeriv ω)
  is_linear := fun c ω₁ ω₂ => by
    -- Expand `d(c•ω₁ + ω₂)` using linearity of `d`.
    have h_d : smoothExtDeriv (c • ω₁ + ω₂) = (c : ℂ) • smoothExtDeriv ω₁ + smoothExtDeriv ω₂ := by
      rw [smoothExtDeriv_add]
      -- `c•ω₁` (ℝ-scalar) is definitionally `((c:ℂ)•ω₁)`
      have h_smul : smoothExtDeriv (c • ω₁) = (c : ℂ) • smoothExtDeriv ω₁ := by
        simpa using (smoothExtDeriv_smul (n := n) (X := X) (k := k) (c : ℂ) ω₁)
      simp [h_smul]
    -- Now use linearity of `T` (over ℝ) on the resulting combination.
    -- Note: `(c:ℂ)•α` is definitional equal to `c•α` for the ℝ-action on `SmoothForm`.
    have hT := T.is_linear c (smoothExtDeriv ω₁) (smoothExtDeriv ω₂)
    -- combine `h_d` and `hT`
    calc
      T.toFun (smoothExtDeriv (c • ω₁ + ω₂))
          = T.toFun ((c : ℂ) • smoothExtDeriv ω₁ + smoothExtDeriv ω₂) := by
              simpa [h_d]
      _ = c * T.toFun (smoothExtDeriv ω₁) + T.toFun (smoothExtDeriv ω₂) := by
              simpa using hT
}

/-- A current is a cycle if its boundary is zero. -/
def isCycle (T : Current n X (k + 1)) : Prop := T.boundary = 0

/-- ∂∂ = 0: boundary of boundary is zero. -/
theorem boundary_boundary (T : Current n X (k + 2)) : (boundary (boundary T)) = 0 := by
  ext ω
  simp only [boundary]
  -- (∂∂T)(ω) = (∂T)(dω) = T(ddω) = T(0) = 0
  have h_dd := smoothExtDeriv_extDeriv ω
  rw [h_dd]
  -- T(0) = 0 follows from linearity (same argument as in `map_smul`).
  have h0' := T.is_linear 1 (0 : SmoothForm n X (k + 2)) 0
  have h0 : T.toFun (0 : SmoothForm n X (k + 2)) = 0 := by
    have ha : T.toFun (0 : SmoothForm n X (k + 2)) =
        T.toFun (0 : SmoothForm n X (k + 2)) + T.toFun (0 : SmoothForm n X (k + 2)) := by
      simpa using h0'
    have ha' : T.toFun (0 : SmoothForm n X (k + 2)) + 0 =
        T.toFun (0 : SmoothForm n X (k + 2)) + T.toFun (0 : SmoothForm n X (k + 2)) := by
      simpa [add_zero] using ha
    have : 0 = T.toFun (0 : SmoothForm n X (k + 2)) := add_left_cancel ha'
    simpa using this.symm
  -- Finish by rewriting the left-hand side and observing the RHS is definitionally 0.
  rw [h0]
  rfl

end Current

end
