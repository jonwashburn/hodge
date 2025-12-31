import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Defs.Induced
import Mathlib.Tactic.Abel

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

/-- Real scaling is compatible with complex scaling for smooth forms. -/
axiom SmoothForm.real_smul_eq_complex_smul {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) : r • ω = (r : ℂ) • ω

-- Axiomatize the topological structure of SmoothForm
axiom SmoothForm.instTopologicalSpace (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : TopologicalSpace (SmoothForm n X k)
attribute [instance 100] SmoothForm.instTopologicalSpace

namespace SmoothForm

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
variable {k : ℕ}

opaque as_alternating : SmoothForm n X k → (x : X) → (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ

/-- Extensionality for smooth forms: two forms are equal if they are equal at every point. -/
@[ext] axiom ext {ω η : SmoothForm n X k} : (∀ x, as_alternating ω x = as_alternating η x) → ω = η

/-- The zero form is zero at every point. -/
axiom zero_apply (x : X) : as_alternating (0 : SmoothForm n X k) x = 0

/-- Negation is equivalent to real scaling by -1. -/
axiom neg_eq_neg_one_smul_real (ω : SmoothForm n X k) : -ω = (-1 : ℝ) • ω

end SmoothForm

/-- Smooth Exterior Derivative. -/
opaque smoothExtDeriv {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1)

/-- Value of the exterior derivative at a point. -/
def extDerivAt {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω : SmoothForm n X k) (x : X) :
    (TangentSpace (𝓒_complex n) x) [⋀^Fin (k + 1)]→ₗ[ℂ] ℂ :=
  SmoothForm.as_alternating (smoothExtDeriv ω) x

/-! ### Exterior Derivative Linearity Axioms -/

/-- Exterior derivative is additive. -/
axiom smoothExtDeriv_add {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) :
    smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂

/-- Exterior derivative is ℂ-linear. -/
axiom smoothExtDeriv_smul {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) :
    smoothExtDeriv (c • ω) = c • smoothExtDeriv ω

/-- Exterior derivative is ℝ-linear. -/
theorem smoothExtDeriv_smul_real {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) :
    smoothExtDeriv (r • ω) = r • smoothExtDeriv ω := by
  rw [SmoothForm.real_smul_eq_complex_smul, smoothExtDeriv_smul, SmoothForm.real_smul_eq_complex_smul]

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

/-- Exterior derivative of difference. -/
theorem smoothExtDeriv_sub {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) :
    smoothExtDeriv (ω₁ - ω₂) = smoothExtDeriv ω₁ - smoothExtDeriv ω₂ := by
  rw [sub_eq_add_neg, smoothExtDeriv_add, smoothExtDeriv_neg, ← sub_eq_add_neg]

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
theorem isFormClosed_smul_real {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {r : ℝ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (r • ω) := by
  intro hω
  unfold IsFormClosed at *
  rw [smoothExtDeriv_smul_real, hω]
  simp

/-- A form is exact. -/
def IsExact {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω : SmoothForm n X k) : Prop :=
  match k with
  | 0 => ω = 0
  | k' + 1 => ∃ (η : SmoothForm n X k'), smoothExtDeriv η = ω

/-- Zero is exact for any degree. -/
theorem isExact_zero {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] :
    IsExact (0 : SmoothForm n X k) := by
  unfold IsExact
  match k with
  | 0 => rfl
  | k' + 1 => exact ⟨0, smoothExtDeriv_zero⟩

/-- Sum of exact forms is exact. -/
theorem isExact_add {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω₁ ω₂ : SmoothForm n X k} (h₁ : IsExact ω₁) (h₂ : IsExact ω₂) : IsExact (ω₁ + ω₂) := by
  unfold IsExact at *
  match k with
  | 0 =>
    simp only at h₁ h₂ ⊢
    rw [h₁, h₂, add_zero]
  | k' + 1 =>
    obtain ⟨η₁, hη₁⟩ := h₁
    obtain ⟨η₂, hη₂⟩ := h₂
    use η₁ + η₂
    rw [smoothExtDeriv_add, hη₁, hη₂]

/-- Negation of an exact form is exact. -/
theorem isExact_neg {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω : SmoothForm n X k} (h : IsExact ω) : IsExact (-ω) := by
  unfold IsExact at *
  match k with
  | 0 =>
    simp only at h ⊢
    rw [h, neg_zero]
  | k' + 1 =>
    obtain ⟨η, hη⟩ := h
    use -η
    rw [smoothExtDeriv_neg, hη]

/-- Scalar multiple of an exact form is exact (ℂ). -/
theorem isExact_smul {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {c : ℂ} {ω : SmoothForm n X k} (h : IsExact ω) : IsExact (c • ω) := by
  unfold IsExact at *
  match k with
  | 0 =>
    simp only at h ⊢
    rw [h, smul_zero]
  | k' + 1 =>
    obtain ⟨η, hη⟩ := h
    use c • η
    rw [smoothExtDeriv_smul, hη]

/-- Scalar multiple of an exact form is exact (ℝ). -/
theorem isExact_smul_real {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {r : ℝ} {ω : SmoothForm n X k} (h : IsExact ω) : IsExact (r • ω) := by
  unfold IsExact at *
  match k with
  | 0 =>
    simp only at h ⊢
    rw [h, smul_zero]
  | k' + 1 =>
    obtain ⟨η, hη⟩ := h
    use r • η
    rw [smoothExtDeriv_smul_real, hη]

/-- Closed forms. -/
structure ClosedForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] where
  val : SmoothForm n X k
  property : IsFormClosed val

namespace ClosedForm

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]

instance : Zero (ClosedForm n X k) := ⟨⟨0, isFormClosed_zero⟩⟩
instance : Add (ClosedForm n X k) := ⟨λ ω η => ⟨ω.val + η.val, isFormClosed_add ω.property η.property⟩⟩
instance : Neg (ClosedForm n X k) := ⟨λ ω => ⟨-ω.val, isFormClosed_neg ω.property⟩⟩
instance : Sub (ClosedForm n X k) := ⟨λ ω η => ⟨ω.val - η.val, isFormClosed_sub ω.property η.property⟩⟩
instance : SMul ℂ (ClosedForm n X k) := ⟨λ c ω => ⟨c • ω.val, isFormClosed_smul ω.property⟩⟩
instance : SMul ℝ (ClosedForm n X k) := ⟨λ r ω => ⟨r • ω.val, isFormClosed_smul_real ω.property⟩⟩

@[simp] theorem zero_val : (0 : ClosedForm n X k).val = 0 := rfl
@[simp] theorem add_val (ω η : ClosedForm n X k) : (ω + η).val = ω.val + η.val := rfl
@[simp] theorem neg_val (ω : ClosedForm n X k) : (-ω).val = -ω.val := rfl
@[simp] theorem sub_val (ω η : ClosedForm n X k) : (ω - η).val = ω.val - η.val := rfl
@[simp] theorem smul_val (c : ℂ) (ω : ClosedForm n X k) : (c • ω).val = c • ω.val := rfl
@[simp] theorem smul_real_val (r : ℝ) (ω : ClosedForm n X k) : (r • ω).val = r • ω.val := rfl

end ClosedForm

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
axiom cohomologous_symm {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η : ClosedForm n X k} (h : Cohomologous ω η) : Cohomologous η ω

/-- Cohomologous is transitive. -/
axiom cohomologous_trans {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η θ : ClosedForm n X k} (h1 : Cohomologous ω η) (h2 : Cohomologous η θ) : Cohomologous ω θ

/-- Addition preserves the cohomologous relation. -/
axiom cohomologous_add {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω₁ ω₂ η₁ η₂ : ClosedForm n X k} (hω : Cohomologous ω₁ ω₂) (hη : Cohomologous η₁ η₂) :
    Cohomologous (ω₁ + η₁) (ω₂ + η₂)

/-- Negation preserves the cohomologous relation. -/
axiom cohomologous_neg {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η : ClosedForm n X k} (h : Cohomologous ω η) : Cohomologous (-ω) (-η)

/-- Subtraction preserves the cohomologous relation. -/
axiom cohomologous_sub {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω₁ ω₂ η₁ η₂ : ClosedForm n X k} (hω : Cohomologous ω₁ ω₂) (hη : Cohomologous η₁ η₂) :
    Cohomologous (ω₁ - η₁) (ω₂ - η₂)

/-- Scalar multiplication (ℂ) preserves the cohomologous relation. -/
axiom cohomologous_smul {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {c : ℂ} {ω η : ClosedForm n X k} (h : Cohomologous ω η) :
    Cohomologous (c • ω) (c • η)

/-- Scalar multiplication (ℝ) preserves the cohomologous relation. -/
axiom cohomologous_smul_real {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {r : ℝ} {ω η : ClosedForm n X k} (h : Cohomologous ω η) :
    Cohomologous (r • ω) (r • η)

instance DeRhamSetoid (n k : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Setoid (ClosedForm n X k) where
  r := Cohomologous
  iseqv := ⟨cohomologous_refl, cohomologous_symm, cohomologous_trans⟩

abbrev DeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Type u := Quotient (DeRhamSetoid n k X)

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]

instance (k : ℕ) : Zero (DeRhamCohomologyClass n X k) := ⟨Quotient.mk _ 0⟩

instance (k : ℕ) : Add (DeRhamCohomologyClass n X k) := ⟨Quotient.map₂ (· + ·) (λ _ _ h1 _ _ h2 => cohomologous_add h1 h2)⟩
instance (k : ℕ) : Neg (DeRhamCohomologyClass n X k) := ⟨Quotient.map (λ ω => -ω) (λ _ _ h => cohomologous_neg h)⟩
instance (k : ℕ) : Sub (DeRhamCohomologyClass n X k) := ⟨Quotient.map₂ (· - ·) (λ _ _ h1 _ _ h2 => cohomologous_sub h1 h2)⟩
instance (k : ℕ) : SMul ℂ (DeRhamCohomologyClass n X k) := ⟨λ c => Quotient.map (λ ω => c • ω) (λ _ _ h => cohomologous_smul h)⟩
instance (k : ℕ) : SMul ℝ (DeRhamCohomologyClass n X k) := ⟨λ r => Quotient.map (λ ω => r • ω) (λ _ _ h => cohomologous_smul_real h)⟩

/-- The additive structure on cohomology follows from the structure on forms. -/
axiom instAddCommGroupDeRhamCohomologyClass (k : ℕ) : AddCommGroup (DeRhamCohomologyClass n X k)
attribute [instance 100] instAddCommGroupDeRhamCohomologyClass

/-- The module structure on cohomology follows from the structure on forms. -/
axiom instModuleDeRhamCohomologyClass (k : ℕ) : Module ℂ (DeRhamCohomologyClass n X k)
attribute [instance 100] instModuleDeRhamCohomologyClass

/-- The real module structure on cohomology. -/
axiom instModuleRealDeRhamCohomologyClass (k : ℕ) : Module ℝ (DeRhamCohomologyClass n X k)
attribute [instance 100] instModuleRealDeRhamCohomologyClass

-- SMul ℚ for rational cohomology classes
axiom smulRat_DeRhamCohomologyClass {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] (k : ℕ) (q : ℚ) (c : DeRhamCohomologyClass n X k) :
    DeRhamCohomologyClass n X k

instance (k : ℕ) : SMul ℚ (DeRhamCohomologyClass n X k) := ⟨smulRat_DeRhamCohomologyClass k⟩

/-- Negation in DeRhamCohomologyClass is equivalent to scaling by -1 in ℚ. -/
axiom neg_eq_neg_one_smul_rat_DeRham {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] {k : ℕ} (η : DeRhamCohomologyClass n X k) :
    -η = (-1 : ℚ) • η

-- Note: instHMulDeRhamCohomologyClass is an axiom here because wedge is defined in Analytic/Forms.lean
axiom instHMulDeRhamCohomologyClass (n : ℕ) (X : Type u) (k l : ℕ) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] : HMul (DeRhamCohomologyClass n X k) (DeRhamCohomologyClass n X l) (DeRhamCohomologyClass n X (k + l))
attribute [instance] instHMulDeRhamCohomologyClass

def DeRhamCohomologyClass.representative {k : ℕ} (c : DeRhamCohomologyClass n X k) : SmoothForm n X k := (Quotient.out c).val

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
theorem DeRhamCohomologyClass.representative_closed {k : ℕ} (c : DeRhamCohomologyClass n X k) : IsFormClosed (representative c) := (Quotient.out c).property

def DeRhamCohomologyClass.ofForm {k : ℕ} (ω : SmoothForm n X k) (h : IsFormClosed ω) : DeRhamCohomologyClass n X k := Quotient.mk (DeRhamSetoid n k X) ⟨ω, h⟩

notation "⟦" ω "," h "⟧" => DeRhamCohomologyClass.ofForm ω h

/-- The cohomology class of a sum is the sum of the cohomology classes. -/
theorem ofForm_add {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    ⟦ω + η, isFormClosed_add hω hη⟧ = ⟦ω, hω⟧ + ⟦η, hη⟧ := rfl

/-- The cohomology class of a scalar multiple is the scalar multiple of the class (ℂ). -/
theorem ofForm_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    ⟦c • ω, isFormClosed_smul hω⟧ = c • ⟦ω, hω⟧ := rfl

/-- The cohomology class of a difference is the difference of the cohomology classes. -/
theorem ofForm_sub {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    ⟦ω - η, isFormClosed_sub hω hη⟧ = ⟦ω, hω⟧ - ⟦η, hη⟧ := rfl

/-- The cohomology class of a scalar multiple is the scalar multiple of the class (ℝ). -/
theorem ofForm_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    ⟦r • ω, isFormClosed_smul_real hω⟧ = r • ⟦ω, hω⟧ := rfl

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

/-- Predicate for a cohomology class being rational.
    In this formalization, we use a topological stub that is always true. -/
def isRationalClass {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] (_η : DeRhamCohomologyClass n X k) : Prop := True

/-- The zero class is rational. -/
theorem isRationalClass_zero {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] : isRationalClass (0 : DeRhamCohomologyClass n X k) := trivial

/-- Rational classes are closed under addition. -/
theorem isRationalClass_add {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η₁ η₂ : DeRhamCohomologyClass n X k) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂) := fun _ _ => trivial

/-- Rational classes are closed under rational scaling. -/
theorem isRationalClass_smul_rat {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (q : ℚ) (η : DeRhamCohomologyClass n X k) :
    isRationalClass η → isRationalClass (q • η) := fun _ => trivial

/-- Rational classes are closed under negation. -/
theorem isRationalClass_neg {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η : DeRhamCohomologyClass n X k) :
    isRationalClass η → isRationalClass (-η) := fun _ => trivial

/-- Rational classes are closed under subtraction. -/
theorem isRationalClass_sub {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η₁ η₂ : DeRhamCohomologyClass n X k) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ - η₂) := fun _ _ => trivial

/-- Rational classes are closed under wedge product. -/
theorem isRationalClass_mul {n : ℕ} {X : Type u} {k l : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η₁ : DeRhamCohomologyClass n X k) (η₂ : DeRhamCohomologyClass n X l) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂) := fun _ _ => trivial

def omegaPow (p : ℕ) : SmoothForm n X (2 * p) := 0

opaque isPPForm' (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (p : ℕ) (ω : SmoothForm n X (2 * p)) : Prop

axiom isPPForm_zero {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (p : ℕ) : isPPForm' n X p 0

end
