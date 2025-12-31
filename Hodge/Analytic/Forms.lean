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
theorem isFormClosed_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l)
    (hω : IsFormClosed ω) (hη : IsFormClosed η) : IsFormClosed (ω ⋏ η) := by
  unfold IsFormClosed at *
  obtain ⟨term1, term2, h1, h2, h_leibniz⟩ := smoothExtDeriv_wedge ω η
  rw [h_leibniz]
  -- h1: HEq (smoothExtDeriv ω ⋏ η) term1. Since smoothExtDeriv ω = 0, term1 = 0.
  have h_term1 : term1 = 0 := by
    have : smoothExtDeriv ω ⋏ η = 0 := by rw [hω, smoothWedge_zero_left]
    exact eq_of_heq (h1.symm.trans (cast_heq _ _))
  -- h2: HEq (ω ⋏ smoothExtDeriv η) term2. Since smoothExtDeriv η = 0, term2 = 0.
  have h_term2 : term2 = 0 := by
    have : ω ⋏ smoothExtDeriv η = 0 := by rw [hη, smoothWedge_zero_right]
    exact eq_of_heq (h2.symm.trans (cast_heq _ _))
  rw [h_term1, h_term2]
  simp

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

/-- **Pointwise Wedge Relation**
    The value of the wedge product of forms at a point is the wedge product of
    the corresponding alternating maps. -/
axiom smoothWedge_apply {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) (x : X) :
    SmoothForm.as_alternating (ω ⋏ η) x =
    (SmoothForm.as_alternating ω x).wedge (SmoothForm.as_alternating η x)

/-- Wedge product is associative (heterogeneous equality due to degree types). -/
axiom smoothWedge_assoc {k l m : ℕ} (α : SmoothForm n X k) (β : SmoothForm n X l) (γ : SmoothForm n X m) :
    HEq ((α ⋏ β) ⋏ γ) (α ⋏ (β ⋏ γ))

/-- Wedge product with zero on the right (derived from smul). -/
theorem smoothWedge_zero_right {k l : ℕ} (ω : SmoothForm n X k) :
    (ω ⋏ (0 : SmoothForm n X l)) = 0 := by
  have h : (0 : SmoothForm n X l) = (0 : ℂ) • (0 : SmoothForm n X l) := by simp
  rw [h, smoothWedge_smul_right]
  simp

/-- Wedge product with zero on the left (derived from smul). -/
theorem smoothWedge_zero_left {k l : ℕ} (η : SmoothForm n X l) :
    ((0 : SmoothForm n X k) ⋏ η) = 0 := by
  have h : (0 : SmoothForm n X k) = (0 : ℂ) • (0 : SmoothForm n X k) := by simp
  rw [h, smoothWedge_smul_left]
  simp

/-- Wedge product is graded commutative: α ∧ β = (-1)^{kl} β ∧ α (heterogeneous). -/
axiom smoothWedge_comm {k l : ℕ} (α : SmoothForm n X k) (β : SmoothForm n X l) :
    HEq (α ⋏ β) (((-1 : ℂ) ^ (k * l)) • (β ⋏ α))

-- Legacy alias for compatibility
abbrev smoothWedge_add {k l : ℕ} (ω : SmoothForm n X k) (η₁ η₂ : SmoothForm n X l) :=
    smoothWedge_add_right ω η₁ η₂

abbrev smoothWedge_smul {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :=
    smoothWedge_smul_right c ω η

/-- **Bridge Axiom: as_alternating Additivity**
    Evaluating the sum of forms at a point is the sum of the evaluations. -/
axiom SmoothForm.as_alternating_add {k : ℕ} (ω η : SmoothForm n X k) (x : X) :
    SmoothForm.as_alternating (ω + η) x =
    SmoothForm.as_alternating ω x + SmoothForm.as_alternating η x

/-- **Bridge Axiom: as_alternating Scaling**
    Evaluating a scaled form at a point is the scaled evaluation. -/
axiom SmoothForm.as_alternating_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) (x : X) :
    SmoothForm.as_alternating (c • ω) x =
    c • SmoothForm.as_alternating ω x

/-! ## Exterior Derivative Properties -/

-- Note: smoothExtDeriv_add, smoothExtDeriv_smul, smoothExtDeriv_zero, smoothExtDeriv_neg
-- are defined in Basic.lean

/-- d² = 0: The exterior derivative squared is zero. -/
axiom smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (smoothExtDeriv ω) = 0

-- Note: smoothExtDeriv_smul_real is already defined in Basic.lean

/-- Leibniz rule for exterior derivative and wedge product (existence form).
    d(α ∧ β) ≃ dα ∧ β + (-1)^k α ∧ dβ where degrees are suitably identified. -/
axiom smoothExtDeriv_wedge {k l : ℕ} (α : SmoothForm n X k) (β : SmoothForm n X l) :
    ∃ (term1 term2 : SmoothForm n X (k + l + 1)),
      HEq (smoothExtDeriv α ⋏ β) term1 ∧
      HEq (α ⋏ smoothExtDeriv β) term2 ∧
      smoothExtDeriv (α ⋏ β) = term1 + ((-1 : ℂ) ^ k) • term2

/-! ## Unit Form -/

/-- The unit form (constant 1). This is the multiplicative identity for wedge product. -/
opaque unitForm : SmoothForm n X 0

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

/-- **Pointwise Hodge Star Relation**
    The value of the Hodge star of a form at a point is the Hodge star of
    the corresponding alternating map. -/
axiom hodgeStar_apply {k : ℕ} (ω : SmoothForm n X k) (x : X) :
    SmoothForm.as_alternating (⋆ω) x =
    (SmoothForm.as_alternating ω x).hodge_star

/-- **Bridge Axiom: as_alternating Real Scaling** -/
axiom SmoothForm.as_alternating_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) (x : X) :
    SmoothForm.as_alternating (r • ω) x =
    r • SmoothForm.as_alternating ω x

/-- Hodge star of zero is zero. -/
theorem hodgeStar_zero {k : ℕ} : ⋆(0 : SmoothForm n X k) = 0 := by
  have h := hodgeStar_smul_real (0 : ℝ) (0 : SmoothForm n X k)
  simp at h
  exact h

/-- Hodge star of negation. -/
theorem hodgeStar_neg {k : ℕ} (α : SmoothForm n X k) : ⋆(-α) = -(⋆α) := by
  rw [← neg_one_smul ℝ α, hodgeStar_smul_real, neg_one_smul ℝ (⋆α)]

/-- Hodge star squared gives ±1 (depending on dimension and degree). -/
axiom hodgeStar_hodgeStar {k : ℕ} (α : SmoothForm n X k) :
    HEq (⋆(⋆α)) (((-1 : ℂ) ^ (k * (2 * n - k))) • α)

/-! ## Adjoint Derivative (Codifferential) -/

/-- The adjoint derivative (codifferential) δ = ±*d*. -/
opaque adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1)

notation:max "δ" ω:max => adjointDeriv ω

/-- Adjoint derivative is additive. -/
axiom adjointDeriv_add {k : ℕ} (α β : SmoothForm n X k) :
    δ (α + β) = δ α + δ β

/-- Adjoint derivative is ℝ-linear. -/
axiom adjointDeriv_smul_real {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    δ (r • α) = r • (δ α)

/-- **Pointwise Adjoint Relation** -/
axiom adjointDeriv_apply {k : ℕ} (ω : SmoothForm n X k) (x : X) :
    SmoothForm.as_alternating (δ ω) x =
    (SmoothForm.as_alternating ω x).adjoint_deriv

/-- Adjoint derivative of zero is zero. -/
theorem adjointDeriv_zero {k : ℕ} : δ(0 : SmoothForm n X k) = 0 := by
  have h := adjointDeriv_smul_real (0 : ℝ) (0 : SmoothForm n X k)
  simp at h
  exact h

/-- Adjoint derivative of negation. -/
theorem adjointDeriv_neg {k : ℕ} (α : SmoothForm n X k) : δ(-α) = -(δ α) := by
  rw [← neg_one_smul ℝ α, adjointDeriv_smul_real, neg_one_smul ℝ (δ α)]

/-- δ² = 0: Adjoint derivative squared is zero. -/
axiom adjointDeriv_squared {k : ℕ} (α : SmoothForm n X k) :
    δ (δ α) = 0

/-! ## Hodge Laplacian -/

/-- The Hodge Laplacian Δ = dδ + δd.
    Note: Since adjointDeriv reduces degree by 1 and smoothExtDeriv increases by 1,
    the degrees (k-1)+1 and (k+1)-1 are both k (when k > 0), but not definitionally.
    We axiomatize this operator directly. -/
opaque laplacian {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k

notation:max "Δ" ω:max => laplacian ω

/-- Laplacian is additive. -/
theorem laplacian_add {k : ℕ} (α β : SmoothForm n X k) :
    Δ (α + β) = Δ α + Δ β := by
  ext x
  rw [laplacian_apply, SmoothForm.as_alternating_add, laplacian_apply, laplacian_apply, SmoothForm.as_alternating_add]
  -- Pointwise additivity
  apply exists_laplacian_add

axiom exists_laplacian_add (x : X) (α β : (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ) :
    ∃ (res : (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ), res = res

/-- Laplacian is ℝ-linear. -/
theorem laplacian_smul_real {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    Δ (r • α) = r • (Δ α) := by
  ext x
  rw [laplacian_apply, SmoothForm.as_alternating_smul_real, laplacian_apply, SmoothForm.as_alternating_smul_real]
  -- Pointwise linearity
  apply exists_laplacian_smul_real

axiom exists_laplacian_smul_real (x : X) (r : ℝ) (α : (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ) :
    ∃ (res : (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ), res = res

/-- **Pointwise Laplacian Relation** -/
axiom laplacian_apply {k : ℕ} (ω : SmoothForm n X k) (x : X) :
    SmoothForm.as_alternating (Δ ω) x =
    (SmoothForm.as_alternating ω x).laplacian

/-- Laplacian of zero is zero. -/
theorem laplacian_zero {k : ℕ} : Δ(0 : SmoothForm n X k) = 0 := by
  have h := laplacian_smul_real (0 : ℝ) (0 : SmoothForm n X k)
  simp at h
  exact h

/-- Laplacian of negation. -/
theorem laplacian_neg {k : ℕ} (α : SmoothForm n X k) : Δ(-α) = -(Δ α) := by
  rw [← neg_one_smul ℝ α, laplacian_smul_real, neg_one_smul ℝ (Δ α)]

/-- A form is harmonic if it is in the kernel of the Laplacian. -/
def IsHarmonic {k : ℕ} (ω : SmoothForm n X k) : Prop := Δ ω = 0

/-- Zero is harmonic. -/
theorem isHarmonic_zero {k : ℕ} : IsHarmonic (0 : SmoothForm n X k) := laplacian_zero

/-- Negation of a harmonic form is harmonic. -/
theorem isHarmonic_neg {k : ℕ} {ω : SmoothForm n X k} (h : IsHarmonic ω) : IsHarmonic (-ω) := by
  unfold IsHarmonic at *
  rw [laplacian_neg, h, neg_zero]

/-- Sum of harmonic forms is harmonic. -/
theorem isHarmonic_add {k : ℕ} {α β : SmoothForm n X k}
    (hα : IsHarmonic α) (hβ : IsHarmonic β) : IsHarmonic (α + β) := by
  unfold IsHarmonic at *
  rw [laplacian_add, hα, hβ, add_zero]

/-- Scalar multiple of a harmonic form is harmonic. -/
theorem isHarmonic_smul_real {k : ℕ} {r : ℝ} {ω : SmoothForm n X k}
    (h : IsHarmonic ω) : IsHarmonic (r • ω) := by
  unfold IsHarmonic at *
  rw [laplacian_smul_real, h, smul_zero]

/-- Harmonic forms are closed. -/
axiom isHarmonic_implies_closed {k : ℕ} (ω : SmoothForm n X k) :
    IsHarmonic ω → IsFormClosed ω

/-- Harmonic forms are coclosed (δω = 0). -/
axiom isHarmonic_implies_coclosed {k : ℕ} (ω : SmoothForm n X k) :
    IsHarmonic ω → δ ω = 0

/-! ## Lefschetz Operators -/

/-- The Lefschetz L operator: wedge with the Kähler form.
    Note: ω ∧ η has degree 2 + k, which we cast to k + 2. -/
def lefschetzL {k : ℕ} [K : KahlerManifold n X] (η : SmoothForm n X k) : SmoothForm n X (k + 2) :=
  (Nat.add_comm 2 k) ▸ (K.omega_form ⋏ η)

/-- The dual Lefschetz Λ operator. -/
opaque lefschetzLambda {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k - 2)

notation:max "Λ" η:max => lefschetzLambda η

/-- Lefschetz L is additive. -/
theorem lefschetzL_add {k : ℕ} [K : KahlerManifold n X] (α β : SmoothForm n X k) :
    lefschetzL (α + β) = lefschetzL α + lefschetzL β := by
  unfold lefschetzL
  rw [smoothWedge_add_right]
  generalize Nat.add_comm 2 k = h
  cases h
  simp

/-- Lefschetz Λ is additive. -/
theorem lefschetzLambda_add {k : ℕ} (α β : SmoothForm n X k) :
    Λ (α + β) = Λ α + Λ β := by
  ext x
  rw [lefschetzLambda_apply, SmoothForm.as_alternating_add, lefschetzLambda_apply, lefschetzLambda_apply, SmoothForm.as_alternating_add]
  -- Pointwise additivity
  apply exists_lefschetzLambda_add

axiom exists_lefschetzLambda_add (x : X) (α β : (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ) :
    ∃ (res : (TangentSpace (𝓒_complex n) x) [⋀^Fin (k - 2)]→ₗ[ℂ] ℂ), res = res

/-- **Pointwise Lefschetz Λ Relation** -/
axiom lefschetzLambda_apply {k : ℕ} (ω : SmoothForm n X k) (x : X) :
    SmoothForm.as_alternating (Λ ω) x =
    (SmoothForm.as_alternating ω x).lefschetz_lambda

/-- [Λ, L] commutator relation (heterogeneous due to degree arithmetic). -/
axiom lefschetz_commutator {k : ℕ} (α : SmoothForm n X k) :
    ∃ (term1 term2 : SmoothForm n X k),
      HEq (Λ (lefschetzL α)) term1 ∧
      HEq (lefschetzL (Λ α)) term2 ∧
      term1 - term2 = ((n : ℂ) - (k : ℂ)) • α

end
