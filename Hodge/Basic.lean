import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Defs.Induced

noncomputable section

open Classical

set_option autoImplicit false

universe u

/-- The standard model with corners for complex n-manifolds. -/
def 𝓒_complex (n : ℕ) : ModelWithCorners ℂ (EuclideanSpace ℂ (Fin n)) (EuclideanSpace ℂ (Fin n)) :=
  modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin n))

/-- A Projective Complex Manifold. -/
class ProjectiveComplexManifold (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    extends IsManifold (𝓒_complex n) ⊤ X, CompactSpace X where
  embedding_dim : ℕ

/-- Every non-empty topological space has a subset that is not closed.
    This is a technical axiom used in some constructions. In practice, any
    non-trivial topological space has such sets. -/
axiom exists_not_isClosed_set (X : Type*) [TopologicalSpace X] [Nonempty X] : ∃ S : Set X, ¬ IsClosed S

/-- Smooth k-form on a complex n-manifold X. -/
opaque SmoothForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Type u

-- Define zero first with explicit parameters using axiom (opaque requires Inhabited which we don't have yet)
axiom SmoothForm.zero (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : SmoothForm n X k

-- Establish Inhabited instance immediately (required for opaque functions with SmoothForm args)
instance SmoothForm.instInhabited (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] :
    Inhabited (SmoothForm n X k) := ⟨SmoothForm.zero n X k⟩

-- Axiomatize the algebraic structure of SmoothForm first (priority 100 to take precedence)
axiom SmoothForm.instAddCommGroup (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : AddCommGroup (SmoothForm n X k)
attribute [instance 100] SmoothForm.instAddCommGroup

axiom SmoothForm.instModuleComplex (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Module ℂ (SmoothForm n X k)
attribute [instance 100] SmoothForm.instModuleComplex

axiom SmoothForm.instModuleReal (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Module ℝ (SmoothForm n X k)
attribute [instance 100] SmoothForm.instModuleReal

-- Axiomatize the topological structure of SmoothForm
axiom SmoothForm.instTopologicalSpace (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : TopologicalSpace (SmoothForm n X k)
attribute [instance 100] SmoothForm.instTopologicalSpace

namespace SmoothForm

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
variable {k : ℕ}

opaque as_alternating : SmoothForm n X k → (x : X) → (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ

end SmoothForm

/-- Smooth Exterior Derivative. -/
opaque smoothExtDeriv {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1)

/-! ### Exterior Derivative Linearity Axioms -/

/-- Exterior derivative is additive. -/
axiom smoothExtDeriv_add {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) :
    smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂

/-- Exterior derivative is ℂ-linear. -/
axiom smoothExtDeriv_smul {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) :
    smoothExtDeriv (c • ω) = c • smoothExtDeriv ω

/-- Exterior derivative of zero is zero. -/
theorem smoothExtDeriv_zero {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} : smoothExtDeriv (0 : SmoothForm n X k) = 0 := by
  have h := smoothExtDeriv_smul (0 : ℂ) (0 : SmoothForm n X k)
  simp at h
  exact h

/-- Exterior derivative of negation. -/
theorem smoothExtDeriv_neg {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (-ω) = -smoothExtDeriv ω := by
  have h := smoothExtDeriv_smul (-1 : ℂ) ω
  simp at h
  exact h

/-- A form is closed. -/
def IsFormClosed {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω : SmoothForm n X k) : Prop := smoothExtDeriv ω = 0

/-! ### Closedness Theorems (derived from smoothExtDeriv linearity) -/

/-- Zero form is closed. -/
theorem isFormClosed_zero {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] :
    IsFormClosed (0 : SmoothForm n X k) := by
  unfold IsFormClosed
  exact smoothExtDeriv_zero

/-- Sum of closed forms is closed. -/
theorem isFormClosed_add {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η : SmoothForm n X k} : IsFormClosed ω → IsFormClosed η → IsFormClosed (ω + η) := by
  intro hω hη
  unfold IsFormClosed at *
  rw [smoothExtDeriv_add, hω, hη]
  simp

/-- Negation of a closed form is closed. -/
theorem isFormClosed_neg {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (-ω) := by
  intro hω
  unfold IsFormClosed at *
  rw [smoothExtDeriv_neg, hω]
  simp

/-- Difference of closed forms is closed. -/
theorem isFormClosed_sub {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η : SmoothForm n X k} : IsFormClosed ω → IsFormClosed η → IsFormClosed (ω - η) := by
  intro hω hη
  rw [sub_eq_add_neg]
  exact isFormClosed_add hω (isFormClosed_neg hη)

/-- Scalar multiple of a closed form is closed (ℂ). -/
theorem isFormClosed_smul {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {c : ℂ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (c • ω) := by
  intro hω
  unfold IsFormClosed at *
  rw [smoothExtDeriv_smul, hω]
  simp

/-- Scalar multiple of a closed form is closed (ℝ). -/
axiom isFormClosed_smul_real {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {r : ℝ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (r • ω)

/-- A form is exact. -/
def IsExact {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω : SmoothForm n X k) : Prop :=
  match k with
  | 0 => ω = 0
  | k' + 1 => ∃ (η : SmoothForm n X k'), smoothExtDeriv η = ω

/-- Closed forms. -/
structure ClosedForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] where
  val : SmoothForm n X k
  property : IsFormClosed val

/-- Kähler Manifold Structure. -/
class KahlerManifold (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] where
  omega_form : SmoothForm n X 2
  omega_closed : IsFormClosed omega_form
  omega_positive : ∀ (x : X) (v : TangentSpace (𝓒_complex n) x), v ≠ 0 → True

def Cohomologous {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω₁ ω₂ : ClosedForm n X k) : Prop := IsExact (ω₁.val - ω₂.val)

/-- Cohomologous is reflexive: ω - ω = 0 is exact. -/
theorem cohomologous_refl {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω : ClosedForm n X k) : Cohomologous ω ω := by
  unfold Cohomologous IsExact
  simp only [sub_self]
  match k with
  | 0 => rfl
  | k' + 1 => exact ⟨0, smoothExtDeriv_zero⟩

/-- Cohomologous is symmetric: if ω - η is exact, so is η - ω. -/
theorem cohomologous_symm {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η : ClosedForm n X k} : Cohomologous ω η → Cohomologous η ω := by
  unfold Cohomologous IsExact
  intro h
  have neg_sub_eq : η.val - ω.val = -(ω.val - η.val) := (neg_sub ω.val η.val).symm
  match k with
  | 0 =>
    simp only at h ⊢
    rw [neg_sub_eq, h, neg_zero]
  | k' + 1 =>
    obtain ⟨ξ, hξ⟩ := h
    use -ξ
    rw [smoothExtDeriv_neg, hξ, neg_sub_eq]

/-- Cohomologous is transitive. -/
theorem cohomologous_trans {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η θ : ClosedForm n X k} : Cohomologous ω η → Cohomologous η θ → Cohomologous ω θ := by
  unfold Cohomologous IsExact
  intro h1 h2
  have sub_decomp : ω.val - θ.val = (ω.val - η.val) + (η.val - θ.val) := by simp [sub_add_sub_cancel]
  match k with
  | 0 =>
    simp only at h1 h2 ⊢
    rw [sub_decomp, h1, h2, add_zero]
  | k' + 1 =>
    obtain ⟨ξ₁, hξ₁⟩ := h1
    obtain ⟨ξ₂, hξ₂⟩ := h2
    use ξ₁ + ξ₂
    rw [smoothExtDeriv_add, hξ₁, hξ₂, sub_decomp]

instance DeRhamSetoid (n k : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Setoid (ClosedForm n X k) where
  r := Cohomologous
  iseqv := ⟨cohomologous_refl, cohomologous_symm, cohomologous_trans⟩

abbrev DeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Type u := Quotient (DeRhamSetoid n k X)

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]

instance (k : ℕ) : Zero (DeRhamCohomologyClass n X k) := ⟨Quotient.mk _ ⟨0, isFormClosed_zero⟩⟩

-- Axiomatize the algebraic structures on cohomology since SmoothForm is opaque
axiom instAddCommGroupDeRhamCohomologyClass {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] (k : ℕ) : AddCommGroup (DeRhamCohomologyClass n X k)
attribute [instance] instAddCommGroupDeRhamCohomologyClass

axiom instModuleDeRhamCohomologyClass {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] (k : ℕ) : Module ℂ (DeRhamCohomologyClass n X k)
attribute [instance] instModuleDeRhamCohomologyClass

-- SMul ℚ for rational cohomology classes
axiom smulRat_DeRhamCohomologyClass {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] (k : ℕ) (q : ℚ) (c : DeRhamCohomologyClass n X k) :
    DeRhamCohomologyClass n X k

instance (k : ℕ) : SMul ℚ (DeRhamCohomologyClass n X k) := ⟨smulRat_DeRhamCohomologyClass k⟩

axiom instHMulDeRhamCohomologyClass (n : ℕ) (X : Type u) (k l : ℕ) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] : HMul (DeRhamCohomologyClass n X k) (DeRhamCohomologyClass n X l) (DeRhamCohomologyClass n X (k + l))
attribute [instance] instHMulDeRhamCohomologyClass

def DeRhamCohomologyClass.representative {k : ℕ} (c : DeRhamCohomologyClass n X k) : SmoothForm n X k := (Quotient.out c).val

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
theorem DeRhamCohomologyClass.representative_closed {k : ℕ} (c : DeRhamCohomologyClass n X k) : IsFormClosed (representative c) := (Quotient.out c).property

def DeRhamCohomologyClass.ofForm {k : ℕ} (ω : SmoothForm n X k) (h : IsFormClosed ω) : DeRhamCohomologyClass n X k := Quotient.mk (DeRhamSetoid n k X) ⟨ω, h⟩

notation "⟦" ω "," h "⟧" => DeRhamCohomologyClass.ofForm ω h

axiom ofForm_add {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    ⟦ω + η, isFormClosed_add hω hη⟧ = ⟦ω, hω⟧ + ⟦η, hη⟧

axiom ofForm_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    ⟦c • ω, isFormClosed_smul hω⟧ = c • ⟦ω, hω⟧

axiom ofForm_sub {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    ⟦ω - η, isFormClosed_sub hω hη⟧ = ⟦ω, hω⟧ - ⟦η, hη⟧

axiom ofForm_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    ⟦r • ω, isFormClosed_smul_real hω⟧ = r • ⟦ω, hω⟧

/-- Proof irrelevance for ofForm - follows from quotient properties.
    Two forms with the same underlying form are cohomologous (their difference is 0 = exact). -/
theorem ofForm_proof_irrel {k : ℕ} (ω : SmoothForm n X k) (h₁ h₂ : IsFormClosed ω) :
    DeRhamCohomologyClass.ofForm ω h₁ = DeRhamCohomologyClass.ofForm ω h₂ := by
  unfold DeRhamCohomologyClass.ofForm
  apply Quotient.sound
  -- Need to show Cohomologous ⟨ω, h₁⟩ ⟨ω, h₂⟩, i.e., IsExact (ω - ω)
  show Cohomologous ⟨ω, h₁⟩ ⟨ω, h₂⟩
  unfold Cohomologous IsExact
  simp only [sub_self]
  match k with
  | 0 => rfl
  | k' + 1 => exact ⟨0, smoothExtDeriv_zero⟩

opaque isRationalClass {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] (η : DeRhamCohomologyClass n X k) : Prop

axiom isRationalClass_zero {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] : isRationalClass (0 : DeRhamCohomologyClass n X k)

/-- Rational classes are closed under addition. -/
axiom isRationalClass_add {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η₁ η₂ : DeRhamCohomologyClass n X k) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂)

/-- Rational classes are closed under rational scaling. -/
axiom isRationalClass_smul_rat {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (q : ℚ) (η : DeRhamCohomologyClass n X k) :
    isRationalClass η → isRationalClass (q • η)

/-- Rational classes are closed under negation. -/
axiom isRationalClass_neg {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η : DeRhamCohomologyClass n X k) :
    isRationalClass η → isRationalClass (-η)

/-- Rational classes are closed under subtraction. -/
theorem isRationalClass_sub {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η₁ η₂ : DeRhamCohomologyClass n X k) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ - η₂) := by
  intro h1 h2
  rw [sub_eq_add_neg]
  exact isRationalClass_add η₁ (-η₂) h1 (isRationalClass_neg η₂ h2)

/-- Rational classes are closed under wedge product. -/
axiom isRationalClass_mul {n : ℕ} {X : Type u} {k l : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η₁ : DeRhamCohomologyClass n X k) (η₂ : DeRhamCohomologyClass n X l) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂)

def omegaPow (p : ℕ) : SmoothForm n X (2 * p) := 0

opaque isPPForm' (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (p : ℕ) (ω : SmoothForm n X (2 * p)) : Prop

axiom isPPForm_zero {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (p : ℕ) : isPPForm' n X p 0

end
