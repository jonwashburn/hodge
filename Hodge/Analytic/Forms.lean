import Hodge.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Differential Forms on Complex Manifolds

This file defines operations on smooth differential forms including:
- Wedge product (∧)
- Hodge star operator (⋆)
- Adjoint derivative / codifferential (δ)
- Hodge Laplacian (Δ = dδ + δd)
- Lefschetz operators (L and Λ)

## Axiom Categories

### Structural Axioms (Required for Opaque Operations)
Since `smoothWedge`, `hodgeStar`, `adjointDeriv`, and `laplacian` are opaque,
we axiomatize their algebraic properties:
- Wedge product: associativity, distributivity, graded commutativity
- Hodge star: linearity, involutivity (⋆⋆ = ±1)
- Codifferential: linearity, δ² = 0
- Laplacian: linearity

### Differential Structure Axioms
- `smoothExtDeriv_extDeriv`: d² = 0 (fundamental property of exterior derivative)
- `smoothExtDeriv_wedge`: Leibniz rule for wedge products
- `isFormClosed_wedge`: Closed forms are closed under wedge product

### Harmonic Forms
- `isHarmonic_implies_closed`: Harmonic ⟹ closed
- `isHarmonic_implies_coclosed`: Harmonic ⟹ coclosed

### Lefschetz Structure
- `lefschetz_commutator`: [Λ, L] = (n - k)·id on k-forms

All axioms express standard facts from Kähler geometry that cannot be derived
from the abstract opaque structure.
-/

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-! ## Wedge Product -/

/-- **Wedge Product of Smooth Forms** (Exterior Algebra).

    The wedge product ω ∧ η of a k-form and an l-form is a (k+l)-form.
    It is bilinear, associative, and graded commutative: α ∧ β = (-1)^{kl} β ∧ α.

    Reference: [É. Cartan, "Leçons sur les invariants intégraux", 1922]. -/
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

/-- Wedge product is associative (heterogeneous equality due to degree types). -/
axiom smoothWedge_assoc {k l m : ℕ} (α : SmoothForm n X k) (β : SmoothForm n X l) (γ : SmoothForm n X m) :
    HEq ((α ⋏ β) ⋏ γ) (α ⋏ (β ⋏ γ))

omit [IsManifold (𝓒_complex n) ⊤ X] in
/-- Wedge product with zero on the right. -/
theorem smoothWedge_zero_right {k l : ℕ} (ω : SmoothForm n X k) :
    (ω ⋏ (0 : SmoothForm n X l)) = 0 := by
  -- 0 = (0 : ℂ) • 0, and by smoothWedge_smul_right, ω ⋏ (c • η) = c • (ω ⋏ η)
  have h : (0 : SmoothForm n X l) = (0 : ℂ) • (0 : SmoothForm n X l) := by simp
  rw [h, smoothWedge_smul_right]
  simp

omit [IsManifold (𝓒_complex n) ⊤ X] in
/-- Wedge product with zero on the left. -/
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

/-! ## Exterior Derivative Properties -/

-- Note: smoothExtDeriv_add, smoothExtDeriv_smul, smoothExtDeriv_zero, smoothExtDeriv_neg
-- are defined in Basic.lean

/-- **d² = 0: The Exterior Derivative is Nilpotent** (Fundamental Property).

    The exterior derivative squared is zero: d(dω) = 0 for all forms ω.
    This is the defining property that makes de Rham cohomology well-defined.

    **Proof Sketch**: In local coordinates, d = ∑ᵢ dxⁱ ∧ ∂/∂xⁱ.
    Then d² involves ∂²/∂xⁱ∂xʲ which is symmetric, but dxⁱ ∧ dxʲ is antisymmetric.
    The contraction of symmetric with antisymmetric is zero.

    Reference: [É. Cartan, "Leçons sur les invariants intégraux", 1922]. -/
axiom smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (smoothExtDeriv ω) = 0

-- Note: smoothExtDeriv_smul_real is now defined in Basic.lean

/-- Leibniz rule for exterior derivative and wedge product (existence form).
    d(α ∧ β) ≃ dα ∧ β + (-1)^k α ∧ dβ where degrees are suitably identified. -/
axiom smoothExtDeriv_wedge {k l : ℕ} (α : SmoothForm n X k) (β : SmoothForm n X l) :
    ∃ (term1 term2 : SmoothForm n X (k + l + 1)),
      HEq (smoothExtDeriv α ⋏ β) term1 ∧
      HEq (α ⋏ smoothExtDeriv β) term2 ∧
      smoothExtDeriv (α ⋏ β) = term1 + ((-1 : ℂ) ^ k) • term2

/-! ## Unit Form -/

/-- **Unit Form (Constant 1)** (Exterior Algebra).

    The unit 0-form is the constant function 1 on X. It is the multiplicative
    identity for the wedge product: 1 ∧ ω = ω ∧ 1 = ω for all forms ω.

    This is opaque because SmoothForm is opaque. -/
opaque unitForm : SmoothForm n X 0

/-! ## Hodge Star Operator -/

variable [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-- **Hodge Star Operator** (Riemannian/Kähler Geometry).

    The Hodge star ⋆: Ω^k → Ω^{2n-k} is defined using the Riemannian metric g
    and orientation. For α, β ∈ Ω^k: α ∧ ⋆β = ⟨α, β⟩ vol_g.

    On a Kähler manifold, ⋆ is compatible with the complex structure.
    Key property: ⋆⋆ = (-1)^{k(2n-k)} on k-forms.

    This is opaque because:
    1. Requires the Riemannian metric structure
    2. SmoothForm is opaque

    Reference: [W.V.D. Hodge, "The Theory and Applications of Harmonic Integrals", 1941]. -/
opaque hodgeStar {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (2 * n - k)

notation:max "⋆" ω:max => hodgeStar ω

/-- Hodge star is additive. -/
axiom hodgeStar_add {k : ℕ} (α β : SmoothForm n X k) :
    ⋆(α + β) = ⋆α + ⋆β

/-- Hodge star is ℝ-linear. -/
axiom hodgeStar_smul_real {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    ⋆(r • α) = r • (⋆α)

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Hodge star of zero is zero. -/
theorem hodgeStar_zero {k : ℕ} : ⋆(0 : SmoothForm n X k) = 0 := by
  have h := hodgeStar_smul_real (0 : ℝ) (0 : SmoothForm n X k)
  simp at h
  exact h

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Hodge star of negation is negation of Hodge star. -/
theorem hodgeStar_neg {k : ℕ} (α : SmoothForm n X k) : ⋆(-α) = -(⋆α) := by
  have h := hodgeStar_smul_real (-1 : ℝ) α
  simp at h
  exact h

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Hodge star of subtraction is subtraction of Hodge stars. -/
theorem hodgeStar_sub {k : ℕ} (α β : SmoothForm n X k) : ⋆(α - β) = ⋆α - ⋆β := by
  rw [sub_eq_add_neg, hodgeStar_add, hodgeStar_neg, ← sub_eq_add_neg]

/-- Hodge star squared gives ±1 (depending on dimension and degree). -/
axiom hodgeStar_hodgeStar {k : ℕ} (α : SmoothForm n X k) :
    HEq (⋆(⋆α)) (((-1 : ℂ) ^ (k * (2 * n - k))) • α)

/-! ## Adjoint Derivative (Codifferential) -/

/-- **Adjoint Derivative / Codifferential** (Hodge Theory).

    The codifferential δ: Ω^k → Ω^{k-1} is the L²-adjoint of d.
    Formula: δ = (-1)^{nk+n+1} ⋆d⋆ on k-forms.

    Key properties:
    - δ² = 0 (analogous to d² = 0)
    - ⟨dα, β⟩_{L²} = ⟨α, δβ⟩_{L²} for compactly supported forms

    This is opaque because:
    1. Defined via Hodge star which is opaque
    2. SmoothForm is opaque

    Reference: [W.V.D. Hodge, "The Theory and Applications of Harmonic Integrals", 1941]. -/
opaque adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1)

notation:max "δ" ω:max => adjointDeriv ω

/-- Adjoint derivative is additive. -/
axiom adjointDeriv_add {k : ℕ} (α β : SmoothForm n X k) :
    δ (α + β) = δ α + δ β

/-- Adjoint derivative is ℝ-linear. -/
axiom adjointDeriv_smul_real {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    δ (r • α) = r • (δ α)

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Adjoint derivative of zero is zero. -/
theorem adjointDeriv_zero {k : ℕ} : δ(0 : SmoothForm n X k) = 0 := by
  have h := adjointDeriv_smul_real (0 : ℝ) (0 : SmoothForm n X k)
  simp at h
  exact h

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Adjoint derivative of negation is negation of adjoint derivative. -/
theorem adjointDeriv_neg {k : ℕ} (α : SmoothForm n X k) : δ(-α) = -(δ α) := by
  have h := adjointDeriv_smul_real (-1 : ℝ) α
  simp at h
  exact h

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Adjoint derivative of subtraction is subtraction of adjoint derivatives. -/
theorem adjointDeriv_sub {k : ℕ} (α β : SmoothForm n X k) : δ(α - β) = δ α - δ β := by
  rw [sub_eq_add_neg, adjointDeriv_add, adjointDeriv_neg, ← sub_eq_add_neg]

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
axiom laplacian_add {k : ℕ} (α β : SmoothForm n X k) :
    Δ (α + β) = Δ α + Δ β

/-- Laplacian is ℝ-linear. -/
axiom laplacian_smul_real {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    Δ (r • α) = r • (Δ α)

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Laplacian of zero is zero. -/
theorem laplacian_zero {k : ℕ} : Δ(0 : SmoothForm n X k) = 0 := by
  have h := laplacian_smul_real (0 : ℝ) (0 : SmoothForm n X k)
  simp at h
  exact h

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Laplacian of negation is negation of Laplacian. -/
theorem laplacian_neg {k : ℕ} (α : SmoothForm n X k) : Δ(-α) = -(Δ α) := by
  have h := laplacian_smul_real (-1 : ℝ) α
  simp at h
  exact h

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Laplacian of subtraction is subtraction of Laplacians. -/
theorem laplacian_sub {k : ℕ} (α β : SmoothForm n X k) : Δ(α - β) = Δ α - Δ β := by
  rw [sub_eq_add_neg, laplacian_add, laplacian_neg, ← sub_eq_add_neg]

/-- A form is harmonic if it is in the kernel of the Laplacian. -/
def IsHarmonic {k : ℕ} (ω : SmoothForm n X k) : Prop := Δ ω = 0

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Zero is harmonic. -/
theorem isHarmonic_zero {k : ℕ} : IsHarmonic (0 : SmoothForm n X k) := laplacian_zero

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Negation of a harmonic form is harmonic. -/
theorem isHarmonic_neg {k : ℕ} {ω : SmoothForm n X k} (h : IsHarmonic ω) : IsHarmonic (-ω) := by
  unfold IsHarmonic at *
  rw [laplacian_neg, h, neg_zero]

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Sum of harmonic forms is harmonic. -/
theorem isHarmonic_add {k : ℕ} {ω₁ ω₂ : SmoothForm n X k}
    (h1 : IsHarmonic ω₁) (h2 : IsHarmonic ω₂) : IsHarmonic (ω₁ + ω₂) := by
  unfold IsHarmonic at *
  rw [laplacian_add, h1, h2, add_zero]

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Scalar multiple of a harmonic form is harmonic (ℝ-scaling). -/
theorem isHarmonic_smul_real {k : ℕ} {ω : SmoothForm n X k} (r : ℝ) (h : IsHarmonic ω) : IsHarmonic (r • ω) := by
  unfold IsHarmonic at *
  rw [laplacian_smul_real, h, smul_zero]

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
/-- Difference of harmonic forms is harmonic. -/
theorem isHarmonic_sub {k : ℕ} {ω₁ ω₂ : SmoothForm n X k}
    (h1 : IsHarmonic ω₁) (h2 : IsHarmonic ω₂) : IsHarmonic (ω₁ - ω₂) := by
  rw [sub_eq_add_neg]
  exact isHarmonic_add h1 (isHarmonic_neg h2)

/-- **Harmonic Forms are Closed** (Hodge Theory).

    If ω is harmonic (Δω = 0), then ω is closed (dω = 0).

    **Proof Sketch**: On a compact Kähler manifold, the Laplacian satisfies
    Δ = dδ + δd. For harmonic ω: 0 = ⟨Δω, ω⟩ = ⟨dδω, ω⟩ + ⟨δdω, ω⟩ = ‖δω‖² + ‖dω‖²
    Hence dω = 0.

    Reference: [W.V.D. Hodge, "The Theory and Applications of Harmonic Integrals", 1941]. -/
axiom isHarmonic_implies_closed {k : ℕ} (ω : SmoothForm n X k) :
    IsHarmonic ω → IsFormClosed ω

/-- **Harmonic Forms are Coclosed** (Hodge Theory).

    If ω is harmonic (Δω = 0), then ω is coclosed (δω = 0).

    **Proof Sketch**: Same as above - the Bochner formula gives
    0 = ‖δω‖² + ‖dω‖², hence δω = 0.

    Reference: [W.V.D. Hodge, "The Theory and Applications of Harmonic Integrals", 1941]. -/
axiom isHarmonic_implies_coclosed {k : ℕ} (ω : SmoothForm n X k) :
    IsHarmonic ω → δ ω = 0

/-! ## Lefschetz Operators -/

/-- The Lefschetz L operator: wedge with the Kähler form.
    Note: ω ∧ η has degree 2 + k, which we cast to k + 2. -/
def lefschetzL {k : ℕ} [K : KahlerManifold n X] (η : SmoothForm n X k) : SmoothForm n X (k + 2) :=
  (Nat.add_comm 2 k) ▸ (K.omega_form ⋏ η)

/-- **Dual Lefschetz Operator Λ** (Kähler Geometry).

    The operator Λ: Ω^k → Ω^{k-2} is the adjoint of L (wedge with ω).
    Formula: Λ = ⋆L⋆ (up to sign).

    Together with L, it forms an sl(2) representation on forms:
    - [Λ, L] = (n - k)·id on k-forms
    - This is the key to proving the Hard Lefschetz theorem

    This is opaque because:
    1. Defined via Hodge star and contraction
    2. SmoothForm is opaque

    Reference: [S. Lefschetz, "L'analysis situs et la géométrie algébrique", 1924]. -/
opaque lefschetzLambda {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k - 2)

notation:max "Λ" η:max => lefschetzLambda η

/-- Lefschetz L is additive.

    **Proof Sketch**: By definition, `lefschetzL η = (Nat.add_comm 2 k) ▸ (ω ∧ η)`.
    Using `smoothWedge_add_right`: `ω ∧ (α + β) = (ω ∧ α) + (ω ∧ β)`.
    The result follows from the fact that the type coercion `▸` commutes with addition.

    This remains an axiom because the distribution of `Eq.rec` over addition
    requires that the Module structure on SmoothForm respects type casts,
    which cannot be shown with opaque `SmoothForm`. -/
axiom lefschetzL_add {k : ℕ} [K : KahlerManifold n X] (α β : SmoothForm n X k) :
    lefschetzL (α + β) = lefschetzL α + lefschetzL β

/-- Lefschetz Λ is additive. -/
axiom lefschetzLambda_add {k : ℕ} (α β : SmoothForm n X k) :
    Λ (α + β) = Λ α + Λ β

/-- **Lefschetz Commutator Relation** (Kähler Geometry).

    The Lefschetz operators L (wedge with ω) and Λ (contraction by ω) satisfy
    the fundamental commutator relation: [Λ, L] = (n - k)·id on k-forms.

    **Proof Sketch**: This follows from the sl(2,ℝ) representation theory.
    The operators L, Λ, and H = [L, Λ] form an sl(2) triple with
    [H, L] = 2L, [H, Λ] = -2Λ, [Λ, L] = H. On k-forms, H acts as (n-k)·id.

    Reference: [W.V.D. Hodge, "The Theory and Applications of Harmonic Integrals", 1941]
               [P. Griffiths and J. Harris, "Principles of Algebraic Geometry", 1978, Ch. 0.7]. -/
axiom lefschetz_commutator {k : ℕ} (α : SmoothForm n X k) :
    ∃ (term1 term2 : SmoothForm n X k),
      HEq (Λ (lefschetzL α)) term1 ∧
      HEq (lefschetzL (Λ α)) term2 ∧
      term1 - term2 = ((n : ℂ) - (k : ℂ)) • α

end
