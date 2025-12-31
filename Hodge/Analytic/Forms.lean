import Hodge.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Track B.1: Differential Forms on Complex Manifolds

This file defines operations on smooth differential forms including:
- Wedge product
- Hodge star operator
- Adjoint derivative (codifferential)
- Laplacian

Since `SmoothForm` is opaque, we axiomatize the key properties.
-/

noncomputable section

open Classical

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-! ## Wedge Product -/

/-- Wedge product of smooth forms. -/
opaque smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    SmoothForm n X (k + l)

notation:67 ω:68 " ⋏ " η:68 => smoothWedge ω η

/-- Wedge product preserves closedness. -/
axiom isFormClosed_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l)
    (hω : IsFormClosed ω) (hη : IsFormClosed η) : IsFormClosed (ω ⋏ η)

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
    HEq ((α ⋏ β) ⋏ γ) (α ⋏ (β ⋏ γ))

/-- Wedge product is zero on the right. -/
axiom smoothWedge_zero_right {k l : ℕ} (ω : SmoothForm n X k) :
    (ω ⋏ (0 : SmoothForm n X l)) = 0

/-- Wedge product is zero on the left. -/
axiom smoothWedge_zero_left {k l : ℕ} (η : SmoothForm n X l) :
    ((0 : SmoothForm n X k) ⋏ η) = 0

/-- Exterior derivative of wedge product (Leibniz rule). -/
axiom smoothExtDeriv_wedge {k l : ℕ} (α : SmoothForm n X k) (β : SmoothForm n X l) :
    ∃ (term1 term2 : SmoothForm n X (k + l + 1)),
      HEq (smoothExtDeriv α ⋏ β) term1 ∧
      HEq (α ⋏ smoothExtDeriv β) term2 ∧
      smoothExtDeriv (α ⋏ β) = term1 + ((-1 : ℂ) ^ k) • term2

/-! ## Unit Form -/

/-- The unit form (constant 1). -/
opaque unitForm : SmoothForm n X 0

/-! ## Hodge Star Operator -/

variable [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-- The Hodge star operator *: Ω^k → Ω^{2n-k}. -/
opaque hodgeStar {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (2 * n - k)

notation:max "⋆" ω:max => hodgeStar ω

/-- Hodge star is additive. -/
axiom hodgeStar_add {k : ℕ} (α β : SmoothForm n X k) : ⋆(α + β) = ⋆α + ⋆β

/-- Hodge star is ℝ-linear. -/
axiom hodgeStar_smul_real {k : ℕ} (r : ℝ) (α : SmoothForm n X k) : ⋆(r • α) = r • (⋆α)

/-- Hodge star of zero is zero. -/
axiom hodgeStar_zero {k : ℕ} : ⋆(0 : SmoothForm n X k) = 0

/-- Hodge star of negation. -/
axiom hodgeStar_neg {k : ℕ} (α : SmoothForm n X k) : ⋆(-α) = -(⋆α)

/-- Hodge star squared. -/
axiom hodgeStar_hodgeStar {k : ℕ} (α : SmoothForm n X k) :
    HEq (⋆(⋆α)) (((-1 : ℂ) ^ (k * (2 * n - k))) • α)

/-! ## Adjoint Derivative (Codifferential) -/

/-- Adjoint derivative (codifferential) δ: Ω^k → Ω^{k-1}. -/
opaque adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1)

notation:max "δ" ω:max => adjointDeriv ω

/-- Adjoint derivative is additive. -/
axiom adjointDeriv_add {k : ℕ} (α β : SmoothForm n X k) : δ(α + β) = δ α + δ β

/-- Adjoint derivative is ℝ-linear. -/
axiom adjointDeriv_smul_real {k : ℕ} (r : ℝ) (α : SmoothForm n X k) : δ(r • α) = r • (δ α)

/-- Adjoint derivative of zero is zero. -/
axiom adjointDeriv_zero {k : ℕ} : δ(0 : SmoothForm n X k) = 0

/-- Adjoint derivative of negation. -/
axiom adjointDeriv_neg {k : ℕ} (α : SmoothForm n X k) : δ(-α) = -(δ α)

/-- δ² = 0. -/
axiom adjointDeriv_squared {k : ℕ} (α : SmoothForm n X k) : δ (δ α) = 0

/-! ## Hodge Laplacian -/

/-- The Hodge Laplacian Δ = dδ + δd. -/
opaque laplacian {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k

notation:max "Δ" ω:max => laplacian ω

/-- Laplacian is additive. -/
axiom laplacian_add {k : ℕ} (α β : SmoothForm n X k) : Δ(α + β) = Δ α + Δ β

/-- Laplacian is ℝ-linear. -/
axiom laplacian_smul_real {k : ℕ} (r : ℝ) (α : SmoothForm n X k) : Δ(r • α) = r • (Δ α)

/-- Laplacian of zero is zero. -/
axiom laplacian_zero {k : ℕ} : Δ(0 : SmoothForm n X k) = 0

/-- Laplacian of negation. -/
axiom laplacian_neg {k : ℕ} (α : SmoothForm n X k) : Δ(-α) = -(Δ α)

/-- A form is harmonic if it is in the kernel of the Laplacian. -/
def IsHarmonic {k : ℕ} (ω : SmoothForm n X k) : Prop := Δ ω = 0

/-- Zero is harmonic. -/
theorem isHarmonic_zero {k : ℕ} : IsHarmonic (0 : SmoothForm n X k) := laplacian_zero

/-- Negation of a harmonic form is harmonic. -/
theorem isHarmonic_neg {k : ℕ} {ω : SmoothForm n X k} (h : IsHarmonic ω) : IsHarmonic (-ω) := by
  unfold IsHarmonic at *; rw [laplacian_neg, h, neg_zero]

/-- Sum of harmonic forms is harmonic. -/
theorem isHarmonic_add {k : ℕ} {α β : SmoothForm n X k}
    (hα : IsHarmonic α) (hβ : IsHarmonic β) : IsHarmonic (α + β) := by
  unfold IsHarmonic at *; rw [laplacian_add, hα, hβ, add_zero]

/-- Scalar multiple of a harmonic form is harmonic. -/
theorem isHarmonic_smul_real {k : ℕ} {r : ℝ} {ω : SmoothForm n X k}
    (h : IsHarmonic ω) : IsHarmonic (r • ω) := by
  unfold IsHarmonic at *; rw [laplacian_smul_real, h, smul_zero]

/-- Harmonic forms are closed. -/
axiom isHarmonic_implies_closed {k : ℕ} (ω : SmoothForm n X k) :
    IsHarmonic ω → IsFormClosed ω

/-- Harmonic forms are coclosed (δω = 0). -/
axiom isHarmonic_implies_coclosed {k : ℕ} (ω : SmoothForm n X k) :
    IsHarmonic ω → δ ω = 0

/-! ## Lefschetz Operators -/

/-- The Lefschetz L operator: wedge with the Kähler form. -/
def lefschetzL {k : ℕ} [K : KahlerManifold n X] (η : SmoothForm n X k) : SmoothForm n X (k + 2) :=
  (Nat.add_comm 2 k) ▸ (K.omega_form ⋏ η)

/-- The dual Lefschetz Λ operator. -/
opaque lefschetzLambda {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k - 2)

notation:max "Λ" η:max => lefschetzLambda η

/-- Lefschetz L is additive. -/
axiom lefschetzL_add {k : ℕ} [K : KahlerManifold n X] (α β : SmoothForm n X k) :
    lefschetzL (α + β) = lefschetzL α + lefschetzL β

/-- Lefschetz Λ is additive. -/
axiom lefschetzLambda_add {k : ℕ} (α β : SmoothForm n X k) :
    Λ (α + β) = Λ α + Λ β

/-- [Λ, L] commutator relation. -/
axiom lefschetz_commutator {k : ℕ} (α : SmoothForm n X k) :
    ∃ (term1 term2 : SmoothForm n X k),
      HEq (Λ (lefschetzL α)) term1 ∧
      HEq (lefschetzL (Λ α)) term2 ∧
      term1 - term2 = ((n : ℂ) - (k : ℂ)) • α

end
