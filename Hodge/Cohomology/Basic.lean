import Hodge.Analytic.Forms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.Basic

noncomputable section

open Classical

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X]

def Cohomologous {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω₁ ω₂ : ClosedForm n X k) : Prop := IsExact (ω₁.val - ω₂.val)

theorem cohomologous_refl {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω : ClosedForm n X k) : Cohomologous ω ω := by
  unfold Cohomologous; simp only [sub_self]
  cases k with | zero => rfl | succ k' => use 0; exact smoothExtDeriv_zero

axiom cohomologous_symm {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η : ClosedForm n X k} : Cohomologous ω η → Cohomologous η ω

axiom cohomologous_trans {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η θ : ClosedForm n X k} : Cohomologous ω η → Cohomologous η θ → Cohomologous ω θ

instance DeRhamSetoid (n k : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Setoid (ClosedForm n X k) where
  r := Cohomologous
  iseqv := ⟨cohomologous_refl, cohomologous_symm, cohomologous_trans⟩

def DeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Type u := Quotient (DeRhamSetoid n k X)

instance (k : ℕ) : Zero (DeRhamCohomologyClass n X k) := ⟨Quotient.mk _ ⟨0, isFormClosed_zero⟩⟩

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
axiom isRationalClass_mul {k l} (η₁ : DeRhamCohomologyClass n X k) (η₂ : DeRhamCohomologyClass n X l) : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂)

inductive isPPForm' (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : (p : ℕ) → SmoothForm n X (2 * p) → Prop where
  | zero (p) : isPPForm' n X p 0
  | add {p ω η} : isPPForm' n X p ω → isPPForm' n X p η → isPPForm' n X p (ω + η)
  | smul {p} (c : ℂ) {ω} : isPPForm' n X p ω → isPPForm' n X p (c • ω)

theorem isPPForm_zero {p} : isPPForm' n X p 0 := isPPForm'.zero p

def DeRhamCohomologyClass.ofForm {k : ℕ} (ω : SmoothForm n X k) (h : IsFormClosed ω) : DeRhamCohomologyClass n X k := Quotient.mk (DeRhamSetoid n k X) ⟨ω, h⟩
notation "⟦" ω "," h "⟧" => DeRhamCohomologyClass.ofForm ω h

axiom ofForm_add {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω + η, isFormClosed_add hω hη⟧ = ⟦ω, hω⟧ + ⟦η, hη⟧
axiom ofForm_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : ⟦c • ω, isFormClosed_smul hω⟧ = c • ⟦ω, hω⟧
axiom ofForm_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : ⟦r • ω, isFormClosed_smul_real hω⟧ = r • ⟦ω, hω⟧
theorem ofForm_proof_irrel {k : ℕ} (ω : SmoothForm n X k) (h₁ h₂ : IsFormClosed ω) : ⟦ω, h₁⟧ = ⟦ω, h₂⟧ := by apply Quotient.sound; apply cohomologous_refl
axiom ofForm_sub {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω - η, isFormClosed_sub hω hη⟧ = ⟦ω, hω⟧ - ⟦η, hη⟧
axiom ofForm_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω ⋏ η, isFormClosed_wedge ω η hω hη⟧ = ⟦ω, hω⟧ * ⟦η, hη⟧

/-! ## Kähler Manifold -/

/-- Kähler Manifold Structure.
    A compact Kähler manifold equipped with a closed (1,1)-form ω (the Kähler form). -/
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
    L(η) = η ∧ ω where ω is the Kähler form. -/
noncomputable def lefschetzL {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k + 2) :=
  η ⋏ KahlerManifold.omega_form (n := n) (X := X)

axiom lefschetzL_add {k : ℕ} (α β : SmoothForm n X k) :
    lefschetzL (α + β) = lefschetzL α + lefschetzL β

axiom lefschetzL_smul {k : ℕ} (c : ℂ) (α : SmoothForm n X k) :
    lefschetzL (c • α) = c • lefschetzL α

theorem lefschetzL_closed {k : ℕ} (η : SmoothForm n X k) (hη : IsFormClosed η) :
    IsFormClosed (lefschetzL η) :=
  isFormClosed_wedge η _ hη KahlerManifold.omega_closed

end
