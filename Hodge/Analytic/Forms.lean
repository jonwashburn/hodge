import Hodge.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Track B.1: Differential Forms on Complex Manifolds

This file defines operations on smooth differential forms including:
- Wedge product
- Hodge star operator
- Adjoint derivative (codifferential)
- Laplacian

Since `SmoothForm` is opaque, we axiomatize the key properties and provide
derived theorems where possible.
-/

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-! ## Wedge Product -/

/-- Wedge product of smooth forms. -/
opaque smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    SmoothForm n X (k + l)

-- Wedge notation with proper precedence for arguments
notation:67 ω:68 " ⋏ " η:68 => smoothWedge ω η

/-- Wedge product preserves closedness (Leibniz rule + d²=0). -/
axiom isFormClosed_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω ⋏ η)

/-- Wedge product is right-additive. -/
axiom smoothWedge_add_right {k l : ℕ} (ω : SmoothForm n X k) (η₁ η₂ : SmoothForm n X l) :
    (ω ⋏ (η₁ + η₂)) = (ω ⋏ η₁) + (ω ⋏ η₂)

/-- Wedge product is left-additive. -/
axiom smoothWedge_add_left {k l : ℕ} (ω₁ ω₂ : SmoothForm n X k) (η : SmoothForm n X l) :
    ((ω₁ + ω₂) ⋏ η) = (ω₁ ⋏ η) + (ω₂ ⋏ η)

/-- Wedge product is right ℂ-linear. -/
axiom smoothWedge_smul_right {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    (ω ⋏ (c • η)) = c • (ω ⋏ η)

/-- Wedge product is left ℂ-linear. -/
axiom smoothWedge_smul_left {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    ((c • ω) ⋏ η) = c • (ω ⋏ η)

/-- Wedge product is associative. -/
axiom smoothWedge_assoc {k l m : ℕ} (α : SmoothForm n X k) (β : SmoothForm n X l) (γ : SmoothForm n X m) :
    ((α ⋏ β) ⋏ γ) = α ⋏ (β ⋏ γ)

/-- Wedge product with zero on the right. -/
axiom smoothWedge_zero_right {k l : ℕ} (ω : SmoothForm n X k) :
    (ω ⋏ (0 : SmoothForm n X l)) = 0

/-- Wedge product with zero on the left. -/
axiom smoothWedge_zero_left {k l : ℕ} (η : SmoothForm n X l) :
    ((0 : SmoothForm n X k) ⋏ η) = 0

/-- Wedge product is graded commutative: α ∧ β = (-1)^{kl} β ∧ α -/
axiom smoothWedge_comm {k l : ℕ} (α : SmoothForm n X k) (β : SmoothForm n X l) :
    (α ⋏ β) = ((-1 : ℂ) ^ (k * l)) • (β ⋏ α)

-- Legacy alias for compatibility
abbrev smoothWedge_add {k l : ℕ} (ω : SmoothForm n X k) (η₁ η₂ : SmoothForm n X l) :=
    smoothWedge_add_right ω η₁ η₂

abbrev smoothWedge_smul {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :=
    smoothWedge_smul_right c ω η

/-! ## Exterior Derivative Properties -/

-- Note: smoothExtDeriv_add, smoothExtDeriv_smul, smoothExtDeriv_zero, smoothExtDeriv_neg
-- are defined in Basic.lean

/-- d² = 0: The exterior derivative squared is zero. -/
axiom smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (smoothExtDeriv ω) = 0

/-- Exterior derivative is ℝ-linear. -/
axiom smoothExtDeriv_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) :
    smoothExtDeriv (r • ω) = r • smoothExtDeriv ω

/-- Leibniz rule for exterior derivative and wedge product. -/
axiom smoothExtDeriv_wedge {k l : ℕ} (α : SmoothForm n X k) (β : SmoothForm n X l) :
    smoothExtDeriv (α ⋏ β) = (smoothExtDeriv α ⋏ β) + ((-1 : ℂ) ^ k) • (α ⋏ smoothExtDeriv β)

/-! ## Hodge Star Operator -/

variable [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-- The Hodge star operator *: Ω^k → Ω^{2n-k}. -/
opaque hodgeStar {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (2 * n - k)

notation:max "⋆" ω:max => hodgeStar ω

/-- Hodge star is additive. -/
axiom hodgeStar_add {k : ℕ} (α β : SmoothForm n X k) :
    ⋆(α + β) = ⋆α + ⋆β

/-- Hodge star is ℝ-linear. -/
axiom hodgeStar_smul_real {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    ⋆(r • α) = r • (⋆α)

/-- Hodge star of zero is zero. -/
theorem hodgeStar_zero {k : ℕ} : ⋆(0 : SmoothForm n X k) = 0 := by
  have h := hodgeStar_smul_real (0 : ℝ) (0 : SmoothForm n X k)
  simp at h
  exact h

/-- Hodge star squared gives ±1 (depending on dimension and degree). -/
axiom hodgeStar_hodgeStar {k : ℕ} (α : SmoothForm n X k) :
    ⋆(⋆α) = ((-1 : ℂ) ^ (k * (2 * n - k))) • α

/-! ## Adjoint Derivative (Codifferential) -/

/-- The adjoint derivative (codifferential) δ = ±*d*. -/
opaque adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1)

notation:max "δ" ω:max => adjointDeriv ω

/-- Adjoint derivative is additive. -/
axiom adjointDeriv_add {k : ℕ} (α β : SmoothForm n X k) :
    δ(α + β) = δα + δβ

/-- Adjoint derivative is ℝ-linear. -/
axiom adjointDeriv_smul_real {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    δ(r • α) = r • (δα)

/-- Adjoint derivative of zero is zero. -/
theorem adjointDeriv_zero {k : ℕ} : δ(0 : SmoothForm n X k) = 0 := by
  have h := adjointDeriv_smul_real (0 : ℝ) (0 : SmoothForm n X k)
  simp at h
  exact h

/-- δ² = 0: Adjoint derivative squared is zero. -/
axiom adjointDeriv_squared {k : ℕ} (α : SmoothForm n X k) :
    δ(δα) = 0

/-! ## Hodge Laplacian -/

/-- The Hodge Laplacian Δ = dδ + δd. -/
def laplacian {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k :=
  smoothExtDeriv (adjointDeriv ω) + adjointDeriv (smoothExtDeriv ω)

notation:max "Δ" ω:max => laplacian ω

/-- Laplacian is additive. -/
theorem laplacian_add {k : ℕ} (α β : SmoothForm n X k) :
    Δ(α + β) = Δα + Δβ := by
  unfold laplacian
  rw [smoothExtDeriv_add, adjointDeriv_add, smoothExtDeriv_add, adjointDeriv_add]
  ring

/-- Laplacian is ℝ-linear. -/
theorem laplacian_smul_real {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    Δ(r • α) = r • (Δα) := by
  unfold laplacian
  rw [adjointDeriv_smul_real, smoothExtDeriv_smul_real]
  rw [smoothExtDeriv_smul_real, adjointDeriv_smul_real]
  rw [smul_add]

/-- Laplacian of zero is zero. -/
theorem laplacian_zero {k : ℕ} : Δ(0 : SmoothForm n X k) = 0 := by
  unfold laplacian
  rw [smoothExtDeriv_zero, adjointDeriv_zero, smoothExtDeriv_zero, adjointDeriv_zero]
  simp

/-- A form is harmonic if it is in the kernel of the Laplacian. -/
def IsHarmonic {k : ℕ} (ω : SmoothForm n X k) : Prop := Δω = 0

/-- Zero is harmonic. -/
theorem isHarmonic_zero {k : ℕ} : IsHarmonic (0 : SmoothForm n X k) := laplacian_zero

/-- Harmonic forms are closed. -/
axiom isHarmonic_implies_closed {k : ℕ} (ω : SmoothForm n X k) :
    IsHarmonic ω → IsFormClosed ω

/-- Harmonic forms are coclosed (δω = 0). -/
axiom isHarmonic_implies_coclosed {k : ℕ} (ω : SmoothForm n X k) :
    IsHarmonic ω → δω = 0

/-! ## Lefschetz Operators -/

/-- The Lefschetz L operator: wedge with the Kähler form. -/
def lefschetzL {k : ℕ} [K : KahlerManifold n X] (η : SmoothForm n X k) : SmoothForm n X (k + 2) :=
  K.omega_form ⋏ η

/-- The dual Lefschetz Λ operator. -/
opaque lefschetzLambda {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k - 2)

notation:max "Λ" η:max => lefschetzLambda η

/-- Lefschetz L is additive. -/
theorem lefschetzL_add {k : ℕ} [K : KahlerManifold n X] (α β : SmoothForm n X k) :
    lefschetzL (α + β) = lefschetzL α + lefschetzL β := by
  unfold lefschetzL
  exact smoothWedge_add_right K.omega_form α β

/-- Lefschetz Λ is additive. -/
axiom lefschetzLambda_add {k : ℕ} (α β : SmoothForm n X k) :
    Λ(α + β) = Λα + Λβ

/-- [Λ, L] commutator relation. -/
axiom lefschetz_commutator {k : ℕ} (α : SmoothForm n X k) :
    Λ(lefschetzL α) - lefschetzL (Λα) = ((n : ℂ) - (k : ℂ)) • α

end
