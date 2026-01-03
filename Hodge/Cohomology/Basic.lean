import Hodge.Analytic.Forms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.Basic

noncomputable section

open Classical

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X]

namespace Hodge

/-- The equivalence relation for de Rham cohomology. -/
def Cohomologous {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω₁ ω₂ : ClosedForm n X k) : Prop := IsExact (ω₁.val - ω₂.val)

theorem cohomologous_refl {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω : ClosedForm n X k) : Cohomologous ω ω := by
  unfold Cohomologous IsExact
  simp only [sub_self]
  cases k with | zero => rfl | succ k' => exact ⟨0, isFormClosed_zero⟩

axiom cohomologous_symm {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η : ClosedForm n X k} : Cohomologous ω η → Cohomologous η ω

axiom cohomologous_trans {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η θ : ClosedForm n X k} : Cohomologous ω η → Cohomologous η θ → Cohomologous ω θ

instance DeRhamSetoid (n k : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Setoid (ClosedForm n X k) where
  r := Cohomologous
  iseqv := ⟨cohomologous_refl, cohomologous_symm, cohomologous_trans⟩

/-- De Rham cohomology group of degree k. -/
def DeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Type u := Quotient (DeRhamSetoid n k X)

def ofForm {k : ℕ} (ω : SmoothForm n X k) (h : IsFormClosed ω) : DeRhamCohomologyClass n X k := Quotient.mk _ ⟨ω, h⟩
notation "⟦" ω "," h "⟧" => ofForm ω h

instance (k : ℕ) : Zero (DeRhamCohomologyClass n X k) := ⟨⟦0, isFormClosed_zero⟧⟩

/-! ### Well-definedness axioms -/

axiom cohomologous_add {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω₁ ω₁' ω₂ ω₂' : ClosedForm n X k) (h1 : ω₁ ≈ ω₁') (h2 : ω₂ ≈ ω₂') : (ω₁ + ω₂) ≈ (ω₁' + ω₂')

axiom cohomologous_neg {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω ω' : ClosedForm n X k) (h : ω ≈ ω') : (-ω) ≈ (-ω')

axiom cohomologous_smul {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (c : ℂ) (ω ω' : ClosedForm n X k) (h : ω ≈ ω') :
    (⟨c • ω.val, isFormClosed_smul ω.property⟩ : ClosedForm n X k) ≈ ⟨c • ω'.val, isFormClosed_smul ω'.property⟩

axiom cohomologous_wedge {n k l : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω₁ ω₁' : ClosedForm n X k) (ω₂ ω₂' : ClosedForm n X l) (h1 : ω₁ ≈ ω₁') (h2 : ω₂ ≈ ω₂') :
    (⟨ω₁.val ⋏ ω₂.val, isFormClosed_wedge _ _ ω₁.property ω₂.property⟩ : ClosedForm n X (k + l)) ≈ ⟨ω₁'.val ⋏ ω₂'.val, isFormClosed_wedge _ _ ω₁'.property ω₂'.property⟩

/-! ### Algebraic Instances -/

axiom instAddDeRhamCohomologyClass (k : ℕ) : Add (DeRhamCohomologyClass n X k)
attribute [instance] instAddDeRhamCohomologyClass

axiom instNegDeRhamCohomologyClass (k : ℕ) : Neg (DeRhamCohomologyClass n X k)
attribute [instance] instNegDeRhamCohomologyClass

axiom instSubDeRhamCohomologyClass (k : ℕ) : Sub (DeRhamCohomologyClass n X k)
attribute [instance] instSubDeRhamCohomologyClass

axiom instAddCommGroupDeRhamCohomologyClass (k : ℕ) : AddCommGroup (DeRhamCohomologyClass n X k)
attribute [instance] instAddCommGroupDeRhamCohomologyClass

axiom instSMulComplexDeRhamCohomologyClass (k : ℕ) : SMul ℂ (DeRhamCohomologyClass n X k)
attribute [instance] instSMulComplexDeRhamCohomologyClass

axiom instModuleComplexDeRhamCohomologyClass (k : ℕ) : Module ℂ (DeRhamCohomologyClass n X k)
attribute [instance] instModuleComplexDeRhamCohomologyClass

axiom instSMulRationalDeRhamCohomologyClass (k : ℕ) : SMul ℚ (DeRhamCohomologyClass n X k)
attribute [instance] instSMulRationalDeRhamCohomologyClass

axiom instHMulDeRhamCohomologyClass (k l : ℕ) : HMul (DeRhamCohomologyClass n X k) (DeRhamCohomologyClass n X l) (DeRhamCohomologyClass n X (k + l))
attribute [instance] instHMulDeRhamCohomologyClass

axiom mul_add {k l : ℕ} (a : DeRhamCohomologyClass n X k) (b c : DeRhamCohomologyClass n X l) : a * (b + c) = a * b + a * c
axiom add_mul {k l : ℕ} (a b : DeRhamCohomologyClass n X k) (c : DeRhamCohomologyClass n X l) : (a + b) * c = a * c + b * c
axiom mul_smul {k l : ℕ} (a : DeRhamCohomologyClass n X k) (r : ℂ) (b : DeRhamCohomologyClass n X l) : a * (r • b) = r • (a * b)
axiom smul_mul {k l : ℕ} (r : ℂ) (a : DeRhamCohomologyClass n X k) (b : DeRhamCohomologyClass n X l) : (r • a) * b = r • (a * b)
axiom zero_mul {k l : ℕ} (a : DeRhamCohomologyClass n X l) : (0 : DeRhamCohomologyClass n X k) * a = 0
axiom mul_zero {k l : ℕ} (a : DeRhamCohomologyClass n X k) : a * (0 : DeRhamCohomologyClass n X l) = 0

/-! ## Rational Classes -/

inductive isRationalClass {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] : DeRhamCohomologyClass n X k → Prop where
  | zero : isRationalClass 0
  | add {η₁ η₂} : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂)
  | smul_rat (q : ℚ) {η} : isRationalClass η → isRationalClass (q • η)
  | neg {η} : isRationalClass η → isRationalClass (-η)

theorem isRationalClass_zero {k} : isRationalClass (0 : DeRhamCohomologyClass n X k) := isRationalClass.zero
theorem isRationalClass_add {k} (η₁ η₂ : DeRhamCohomologyClass n X k) : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂) := isRationalClass.add
theorem isRationalClass_smul_rat {k} (q : ℚ) (η : DeRhamCohomologyClass n X k) : isRationalClass η → isRationalClass (q • η) := isRationalClass.smul_rat q
theorem isRationalClass_neg {k} (η : DeRhamCohomologyClass n X k) : isRationalClass η → isRationalClass (-η) := isRationalClass.neg

axiom isRationalClass_sub {k} (η₁ η₂ : DeRhamCohomologyClass n X k) : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ - η₂)
axiom isRationalClass_mul {k l} (η₁ : DeRhamCohomologyClass n X k) (η₂ : DeRhamCohomologyClass n X l) (h1 : isRationalClass η₁) (h2 : isRationalClass η₂) : isRationalClass (η₁ * η₂)

/-! ## Descent Properties -/

axiom ofForm_add {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω + η, isFormClosed_add hω hη⟧ = ⟦ω, hω⟧ + ⟦η, hη⟧
axiom ofForm_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : ⟦c • ω, isFormClosed_smul hω⟧ = c • ⟦ω, hω⟧
axiom ofForm_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : ⟦r • ω, isFormClosed_smul_real hω⟧ = r • ⟦ω, hω⟧

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] in
theorem ofForm_proof_irrel {k : ℕ} (ω : SmoothForm n X k) (h₁ h₂ : IsFormClosed ω) : ⟦ω, h₁⟧ = ⟦ω, h₂⟧ := by apply Quotient.sound; apply cohomologous_refl

axiom ofForm_sub {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω - η, isFormClosed_sub hω hη⟧ = ⟦ω, hω⟧ - ⟦η, hη⟧
axiom ofForm_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω ⋏ η, isFormClosed_wedge ω η hω hη⟧ = ⟦ω, hω⟧ * ⟦η, hη⟧

/-! ## (p,p) Forms -/

inductive isPPForm' (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : (p : ℕ) → SmoothForm n X (2 * p) → Prop where
  | zero (p) : isPPForm' n X p 0
  | add {p ω η} : isPPForm' n X p ω → isPPForm' n X p η → isPPForm' n X p (ω + η)
  | smul {p} (c : ℂ) {ω} : isPPForm' n X p ω → isPPForm' n X p (c • ω)

omit [ProjectiveComplexManifold n X] in
theorem isPPForm_zero {p} : isPPForm' n X p 0 := isPPForm'.zero p

/-! ## Kähler Manifold -/

class KahlerManifold (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] where
  omega_form : SmoothForm n X 2
  omega_closed : IsFormClosed omega_form
  omega_positive : ∀ (x : X) (v : TangentSpace (𝓒_complex n) x), v ≠ 0 → True
  omega_is_pp : isPPForm' n X 1 omega_form
  omega_rational : isRationalClass ⟦omega_form, omega_closed⟧
  omega_J_invariant : ∀ (x : X) (v w : TangentSpace (𝓒_complex n) x),
    omega_form.as_alternating x ![Complex.I • v, Complex.I • w] = omega_form.as_alternating x ![v, w]

/-! ## Lefschetz Operator -/

variable [KahlerManifold n X]

/-- **Lefschetz Operator L** (Kähler Geometry).
    L(η) = ω ∧ η where ω is the Kähler form. -/
noncomputable def lefschetzL {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k + 2) :=
  (Nat.add_comm 2 k) ▸ (KahlerManifold.omega_form (n := n) (X := X) ⋏ η)

axiom lefschetzL_add {k : ℕ} (α β : SmoothForm n X k) :
    lefschetzL (α + β) = lefschetzL α + lefschetzL β

axiom lefschetzL_smul {k : ℕ} (c : ℂ) (α : SmoothForm n X k) :
    lefschetzL (c • α) = c • lefschetzL α

axiom lefschetzL_closed {k : ℕ} (η : SmoothForm n X k) (hη : IsFormClosed η) :
    IsFormClosed (lefschetzL η)

end Hodge

end
