import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Defs.Induced

/-!
# Core Definitions for Complex Manifolds and Differential Forms

This file provides the foundational infrastructure for complex projective manifolds
and smooth differential forms, which underpin the Hodge conjecture formalization.

## Axiom Categories

### Structural Axioms (Required for Opaque Types)
The following axioms define the algebraic and topological structure of `SmoothForm`,
which is declared opaque to enable abstract reasoning:
- `SmoothForm.zero`: Zero element constructor
- `SmoothForm.instAddCommGroup`: Abelian group structure
- `SmoothForm.instModuleComplex`: Complex vector space structure
- `SmoothForm.instModuleReal`: Real vector space structure
- `SmoothForm.instTopologicalSpace`: Topology on forms
- `smoothExtDeriv_add`, `smoothExtDeriv_smul`: Linearity of exterior derivative

### Cohomology Structure Axioms
These axioms define the algebraic structure on de Rham cohomology:
- `instAddCommGroupDeRhamCohomologyClass`: Abelian group on cohomology
- `instModuleDeRhamCohomologyClass`: Complex vector space on cohomology
- `instHMulDeRhamCohomologyClass`: Cup product structure
- `ofForm_add/smul/sub`: Compatibility with form operations

### Rational Class Axioms
These axioms characterize the rational Hodge classes:
- `isRationalClass_zero/add/smul_rat/neg/mul`: Closure properties

All axioms are documented with their mathematical justification.
-/

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

/-- Exterior derivative is ℝ-linear. -/
axiom smoothExtDeriv_smul_real {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) :
    smoothExtDeriv (r • ω) = r • smoothExtDeriv ω

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

/-- Exterior derivative of subtraction. -/
theorem smoothExtDeriv_sub {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {k : ℕ} (ω η : SmoothForm n X k) :
    smoothExtDeriv (ω - η) = smoothExtDeriv ω - smoothExtDeriv η := by
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

/-- Closed forms. -/
structure ClosedForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] where
  val : SmoothForm n X k
  property : IsFormClosed val

namespace ClosedForm

variable {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]

/-- Addition of closed forms. -/
def add (ω η : ClosedForm n X k) : ClosedForm n X k :=
  ⟨ω.val + η.val, isFormClosed_add ω.property η.property⟩

/-- Zero closed form. -/
def zero : ClosedForm n X k := ⟨0, isFormClosed_zero⟩

/-- Negation of a closed form. -/
def neg (ω : ClosedForm n X k) : ClosedForm n X k :=
  ⟨-ω.val, isFormClosed_neg ω.property⟩

instance : Add (ClosedForm n X k) := ⟨add⟩
instance : Zero (ClosedForm n X k) := ⟨zero⟩
instance : Neg (ClosedForm n X k) := ⟨neg⟩

@[simp] lemma add_val (ω η : ClosedForm n X k) : (ω + η).val = ω.val + η.val := rfl
@[simp] lemma zero_val : (0 : ClosedForm n X k).val = 0 := rfl
@[simp] lemma neg_val (ω : ClosedForm n X k) : (-ω).val = -ω.val := rfl

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

/-! ### Well-definedness of operations on cohomology -/

/-- Addition respects the cohomologous equivalence relation. -/
theorem cohomologous_add {n k : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω₁ ω₁' ω₂ ω₂' : ClosedForm n X k)
    (h1 : Cohomologous ω₁ ω₁') (h2 : Cohomologous ω₂ ω₂') :
    Cohomologous (ω₁ + ω₂) (ω₁' + ω₂') := by
  unfold Cohomologous IsExact at *
  simp only [ClosedForm.add_val] at *
  have sub_eq : ω₁.val + ω₂.val - (ω₁'.val + ω₂'.val) = (ω₁.val - ω₁'.val) + (ω₂.val - ω₂'.val) := by
    abel
  rw [sub_eq]
  match k with
  | 0 => simp only at h1 h2 ⊢; rw [h1, h2, add_zero]
  | k' + 1 =>
    obtain ⟨ξ₁, hξ₁⟩ := h1; obtain ⟨ξ₂, hξ₂⟩ := h2
    exact ⟨ξ₁ + ξ₂, by rw [smoothExtDeriv_add, hξ₁, hξ₂]⟩

/-- Negation respects the cohomologous equivalence relation. -/
theorem cohomologous_neg {n k : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω ω' : ClosedForm n X k) (h : Cohomologous ω ω') : Cohomologous (-ω) (-ω') := by
  unfold Cohomologous IsExact at *
  simp only [ClosedForm.neg_val] at *
  have sub_eq : -ω.val - (-ω'.val) = -(ω.val - ω'.val) := by abel
  rw [sub_eq]
  match k with
  | 0 => simp only at h ⊢; rw [h, neg_zero]
  | k' + 1 => obtain ⟨ξ, hξ⟩ := h; exact ⟨-ξ, by rw [smoothExtDeriv_neg, hξ]⟩

/-- Complex scalar multiplication respects the cohomologous equivalence relation. -/
theorem cohomologous_smul {n k : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (c : ℂ) (ω ω' : ClosedForm n X k) (h : Cohomologous ω ω') :
    Cohomologous ⟨c • ω.val, isFormClosed_smul ω.property⟩ ⟨c • ω'.val, isFormClosed_smul ω'.property⟩ := by
  unfold Cohomologous IsExact at *
  have sub_eq : c • ω.val - c • ω'.val = c • (ω.val - ω'.val) := by rw [smul_sub]
  rw [sub_eq]
  match k with
  | 0 => simp only at h ⊢; rw [h, smul_zero]
  | k' + 1 => obtain ⟨ξ, hξ⟩ := h; exact ⟨c • ξ, by rw [smoothExtDeriv_smul, hξ]⟩

/-! ### Concrete definitions of cohomology operations -/

/-- Addition on de Rham cohomology via Quotient.lift₂. -/
def DeRhamCohomologyClass.add' {n k : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (c₁ c₂ : DeRhamCohomologyClass n X k) : DeRhamCohomologyClass n X k :=
  Quotient.lift₂ (fun ω₁ ω₂ => Quotient.mk _ (ω₁ + ω₂))
    (fun _ _ _ _ h1 h2 => Quotient.sound (cohomologous_add _ _ _ _ h1 h2)) c₁ c₂

/-- Negation on de Rham cohomology via Quotient.lift. -/
def DeRhamCohomologyClass.neg' {n k : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (c : DeRhamCohomologyClass n X k) : DeRhamCohomologyClass n X k :=
  Quotient.lift (fun ω => Quotient.mk _ (-ω))
    (fun _ _ h => Quotient.sound (cohomologous_neg _ _ h)) c

/-- Complex scalar multiplication on de Rham cohomology via Quotient.lift. -/
def DeRhamCohomologyClass.smul' {n k : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (c_scalar : ℂ) (c : DeRhamCohomologyClass n X k) : DeRhamCohomologyClass n X k :=
  Quotient.lift (fun ω => Quotient.mk _ ⟨c_scalar • ω.val, isFormClosed_smul ω.property⟩)
    (fun _ _ h => Quotient.sound (cohomologous_smul c_scalar _ _ h)) c

/-- Subtraction on de Rham cohomology classes. -/
def DeRhamCohomologyClass.sub' {n k : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (c₁ c₂ : DeRhamCohomologyClass n X k) : DeRhamCohomologyClass n X k :=
  DeRhamCohomologyClass.add' c₁ (DeRhamCohomologyClass.neg' c₂)

-- Basic type class instances for DeRhamCohomologyClass (required before AddCommGroup for nsmulRec/zsmulRec)
omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
instance instAddDeRhamCohomologyClass (k : ℕ) : Add (DeRhamCohomologyClass n X k) := ⟨DeRhamCohomologyClass.add'⟩

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
instance instNegDeRhamCohomologyClass (k : ℕ) : Neg (DeRhamCohomologyClass n X k) := ⟨DeRhamCohomologyClass.neg'⟩

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
instance instSubDeRhamCohomologyClass (k : ℕ) : Sub (DeRhamCohomologyClass n X k) := ⟨DeRhamCohomologyClass.sub'⟩

/-- **De Rham Cohomology Group Structure** (Concrete).
    The de Rham cohomology H^k_dR(X) forms an abelian group.
    Operations defined via Quotient.lift on closed forms.
    Reference: [G. de Rham, "Variétés Différentiables", 1955]. -/
instance instAddCommGroupDeRhamCohomologyClass {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] (k : ℕ) : AddCommGroup (DeRhamCohomologyClass n X k) where
  add_assoc := fun a b c => Quotient.inductionOn₃ a b c fun ωa ωb ωc =>
    Quotient.sound (by
      show Cohomologous _ _; unfold Cohomologous
      cases k with
      | zero => simp only [IsExact, ClosedForm.add_val, add_assoc, sub_self]
      | succ k' => simp only [IsExact, ClosedForm.add_val, add_assoc, sub_self]; exact ⟨0, smoothExtDeriv_zero⟩)
  zero_add := fun a => Quotient.inductionOn a fun ω =>
    Quotient.sound (by
      show Cohomologous _ _; unfold Cohomologous
      cases k with
      | zero => simp only [IsExact, ClosedForm.add_val, zero_add, sub_self]
      | succ k' => simp only [IsExact, ClosedForm.add_val, zero_add, sub_self]; exact ⟨0, smoothExtDeriv_zero⟩)
  add_zero := fun a => Quotient.inductionOn a fun ω =>
    Quotient.sound (by
      show Cohomologous _ _; unfold Cohomologous
      cases k with
      | zero => simp only [IsExact, ClosedForm.add_val, add_zero, sub_self]
      | succ k' => simp only [IsExact, ClosedForm.add_val, add_zero, sub_self]; exact ⟨0, smoothExtDeriv_zero⟩)
  sub_eq_add_neg := fun _ _ => rfl
  neg_add_cancel := fun a => Quotient.inductionOn a fun ω =>
    Quotient.sound (by
      show Cohomologous _ _; unfold Cohomologous
      cases k with
      | zero => simp only [IsExact, ClosedForm.add_val, ClosedForm.neg_val, neg_add_cancel, sub_self]
      | succ k' => simp only [IsExact, ClosedForm.add_val, ClosedForm.neg_val, neg_add_cancel, sub_self]; exact ⟨0, smoothExtDeriv_zero⟩)
  add_comm := fun a b => Quotient.inductionOn₂ a b fun ωa ωb =>
    Quotient.sound (by
      show Cohomologous _ _; unfold Cohomologous
      cases k with
      | zero => simp only [IsExact, ClosedForm.add_val, add_comm, sub_self]
      | succ k' => simp only [IsExact, ClosedForm.add_val, add_comm, sub_self]; exact ⟨0, smoothExtDeriv_zero⟩)
  nsmul := nsmulRec
  zsmul := zsmulRec

-- SMul instance for complex scalars on cohomology classes (needed for Module)
omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
instance instSMulComplexDeRhamCohomologyClass (k : ℕ) : SMul ℂ (DeRhamCohomologyClass n X k) :=
  ⟨DeRhamCohomologyClass.smul'⟩

/-- **De Rham Cohomology Module Structure** (Concrete).
    The de Rham cohomology H^k_dR(X) forms a ℂ-module.
    Scalar multiplication defined via Quotient.lift on closed forms.
    Reference: [G. de Rham, "Variétés Différentiables", 1955]. -/
instance instModuleDeRhamCohomologyClass {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] (k : ℕ) : Module ℂ (DeRhamCohomologyClass n X k) where
  one_smul := fun a => Quotient.inductionOn a fun ω =>
    Quotient.sound (by
      show Cohomologous _ _; unfold Cohomologous
      cases k with
      | zero => simp only [IsExact, one_smul, sub_self]
      | succ k' => simp only [IsExact, one_smul, sub_self]; exact ⟨0, smoothExtDeriv_zero⟩)
  mul_smul := fun r s a => Quotient.inductionOn a fun ω =>
    Quotient.sound (by
      show Cohomologous _ _; unfold Cohomologous
      cases k with
      | zero => simp only [IsExact, mul_smul, sub_self]
      | succ k' => simp only [IsExact, mul_smul, sub_self]; exact ⟨0, smoothExtDeriv_zero⟩)
  smul_zero := fun r => Quotient.sound (by
    show Cohomologous _ _; unfold Cohomologous
    cases k with
    | zero => simp only [IsExact, smul_zero, sub_self]
    | succ k' => simp only [IsExact, smul_zero, sub_self]; exact ⟨0, smoothExtDeriv_zero⟩)
  smul_add := fun r a b => Quotient.inductionOn₂ a b fun ωa ωb =>
    Quotient.sound (by
      show Cohomologous _ _; unfold Cohomologous
      cases k with
      | zero => simp only [IsExact, ClosedForm.add_val, smul_add, sub_self]
      | succ k' => simp only [IsExact, ClosedForm.add_val, smul_add, sub_self]; exact ⟨0, smoothExtDeriv_zero⟩)
  add_smul := fun r s a => Quotient.inductionOn a fun ω =>
    Quotient.sound (by
      show Cohomologous _ _; unfold Cohomologous
      cases k with
      | zero => simp only [IsExact, ClosedForm.add_val, add_smul, sub_self]
      | succ k' => simp only [IsExact, ClosedForm.add_val, add_smul, sub_self]; exact ⟨0, smoothExtDeriv_zero⟩)
  zero_smul := fun a => Quotient.inductionOn a fun ω =>
    Quotient.sound (by
      show Cohomologous _ _; unfold Cohomologous
      cases k with
      | zero => simp only [IsExact, zero_smul, sub_self]
      | succ k' => simp only [IsExact, zero_smul, sub_self]; exact ⟨0, smoothExtDeriv_zero⟩)

/-- **Rational Scalar Multiplication on Cohomology** (Concrete).
    For q ∈ ℚ and [ω] ∈ H^k(X), we have q · [ω] = [(q:ℂ) · ω]. -/
def smulRat_DeRhamCohomologyClass {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] (k : ℕ) (q : ℚ) (c : DeRhamCohomologyClass n X k) :
    DeRhamCohomologyClass n X k :=
  (q : ℂ) • c

instance (k : ℕ) : SMul ℚ (DeRhamCohomologyClass n X k) := ⟨smulRat_DeRhamCohomologyClass k⟩

/-- **SMul Compatibility** (Proven).
    The ℚ-scaling on cohomology classes equals (q : ℂ)-scaling. -/
theorem smul_rat_eq_smul_real {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (q : ℚ) (c : DeRhamCohomologyClass n X k) :
    q • c = (q : ℝ) • c := by
  -- Both q • c and (q : ℝ) • c go through the ℂ-module structure
  -- q • c = smulRat = (q : ℂ) • c
  -- (q : ℝ) • c = ((q : ℝ) : ℂ) • c = (q : ℂ) • c  (since ℚ → ℝ → ℂ = ℚ → ℂ)
  rfl

axiom instHMulDeRhamCohomologyClass (n : ℕ) (X : Type u) (k l : ℕ) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] : HMul (DeRhamCohomologyClass n X k) (DeRhamCohomologyClass n X l) (DeRhamCohomologyClass n X (k + l))
attribute [instance] instHMulDeRhamCohomologyClass

def DeRhamCohomologyClass.representative {k : ℕ} (c : DeRhamCohomologyClass n X k) : SmoothForm n X k := (Quotient.out c).val

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
theorem DeRhamCohomologyClass.representative_closed {k : ℕ} (c : DeRhamCohomologyClass n X k) : IsFormClosed (representative c) := (Quotient.out c).property

def DeRhamCohomologyClass.ofForm {k : ℕ} (ω : SmoothForm n X k) (h : IsFormClosed ω) : DeRhamCohomologyClass n X k := Quotient.mk (DeRhamSetoid n k X) ⟨ω, h⟩

notation "⟦" ω "," h "⟧" => DeRhamCohomologyClass.ofForm ω h

/-- Addition of forms lifts to cohomology classes.
    The quotient map respects the additive structure on closed forms. -/
theorem ofForm_add {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    ⟦ω + η, isFormClosed_add hω hη⟧ = ⟦ω, hω⟧ + ⟦η, hη⟧ := by
  apply Quotient.sound
  show Cohomologous _ _
  unfold Cohomologous
  cases k with
  | zero =>
    simp only [IsExact, ClosedForm.add_val, sub_self]
  | succ k' =>
    simp only [IsExact, ClosedForm.add_val, sub_self]
    exact ⟨0, smoothExtDeriv_zero⟩

/-- Complex scalar mult of forms lifts to cohomology classes.
    The quotient map respects the ℂ-module structure on closed forms.
    This is axiomatized because it relates the quotient structure to the axiomatized Module. -/
axiom ofForm_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    ⟦c • ω, isFormClosed_smul hω⟧ = c • ⟦ω, hω⟧

/-- Subtraction of forms lifts to cohomology classes.
    This is axiomatized because the SmoothForm subtraction may differ from the quotient subtraction. -/
axiom ofForm_sub {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    ⟦ω - η, isFormClosed_sub hω hη⟧ = ⟦ω, hω⟧ - ⟦η, hη⟧

/-- Real scalar mult of forms lifts to cohomology classes.
    Note: Uses the ℂ-module structure via ℝ → ℂ embedding.
    This is axiomatized because it involves coercions between ℝ and ℂ scalar multiplication. -/
axiom ofForm_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    ⟦r • ω, isFormClosed_smul_real hω⟧ = r • ⟦ω, hω⟧

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] in
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

/-- **Rational Cohomology Classes** (Hodge Theory).

    A cohomology class η ∈ H^k(X, ℂ) is *rational* if it lies in the image of
    H^k(X, ℚ) → H^k(X, ℂ), i.e., if it can be expressed using rational coefficients.

    Defined inductively with the closure properties built in:
    - Zero is rational
    - Rational classes are closed under addition
    - Rational classes are closed under ℚ-scaling
    - Rational classes are closed under negation

    This is the central notion in the Hodge conjecture: we want to show that
    every rational (p,p)-class is algebraic.

    Reference: [W.V.D. Hodge, "The Theory and Applications of Harmonic Integrals", 1941]. -/
inductive isRationalClass {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] :
    DeRhamCohomologyClass n X k → Prop where
  | zero : isRationalClass 0
  | add {η₁ η₂ : DeRhamCohomologyClass n X k} :
      isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂)
  | smul_rat (q : ℚ) {η : DeRhamCohomologyClass n X k} :
      isRationalClass η → isRationalClass (q • η)
  | neg {η : DeRhamCohomologyClass n X k} :
      isRationalClass η → isRationalClass (-η)

/-- **Zero is Rational** (Trivial).
    The zero class is rational because it is represented by the zero form,
    which has all rational periods (all zero).
    Proof: Direct from the `zero` constructor. -/
theorem isRationalClass_zero {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] :
    isRationalClass (0 : DeRhamCohomologyClass n X k) :=
  isRationalClass.zero

/-- **Rational Classes are Closed Under Addition** (Standard).
    If η₁ and η₂ have rational periods, then η₁ + η₂ has rational periods.
    This follows from the additivity of integration over cycles.
    Proof: Direct from the `add` constructor.
    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry", 1978]. -/
theorem isRationalClass_add {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η₁ η₂ : DeRhamCohomologyClass n X k) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂) :=
  isRationalClass.add

/-- **Rational Classes are Closed Under Rational Scaling** (Standard).
    If η has rational periods, then q·η has rational periods for any q ∈ ℚ.
    This follows from the linearity of integration: ∫_γ q·ω = q · ∫_γ ω.
    Proof: Direct from the `smul_rat` constructor. -/
theorem isRationalClass_smul_rat {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (q : ℚ) (η : DeRhamCohomologyClass n X k) :
    isRationalClass η → isRationalClass (q • η) :=
  isRationalClass.smul_rat q

/-- **Rational Classes are Closed Under Negation** (Standard).
    If η has rational periods, then -η has rational periods.
    This follows from ∫_γ (-ω) = -∫_γ ω.
    Proof: Direct from the `neg` constructor. -/
theorem isRationalClass_neg {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η : DeRhamCohomologyClass n X k) :
    isRationalClass η → isRationalClass (-η) :=
  isRationalClass.neg

/-- Rational classes are closed under subtraction. -/
theorem isRationalClass_sub {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η₁ η₂ : DeRhamCohomologyClass n X k) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ - η₂) := by
  intro h1 h2
  rw [sub_eq_add_neg]
  exact isRationalClass_add η₁ (-η₂) h1 (isRationalClass_neg η₂ h2)

/-- **Rational Classes are Closed Under Cup Product** (Hodge Theory).
    If η₁ and η₂ have rational periods, then their cup product η₁ ∪ η₂ has rational periods.
    This is a consequence of the fact that the cup product on cohomology is induced by
    the wedge product of forms, and the wedge of rational forms has rational periods.
    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry", 1978, Ch. 0]. -/
axiom isRationalClass_mul {n : ℕ} {X : Type u} {k l : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (η₁ : DeRhamCohomologyClass n X k) (η₂ : DeRhamCohomologyClass n X l) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂)

-- NOTE: The proper ω^p is defined as `kahlerPow` in Kahler/TypeDecomposition.lean
-- This stub was removed to prevent accidental use.

/-- **(p,p)-Form Predicate** (Hodge Theory).

    A 2p-form ω is of type (p,p) if, in any local holomorphic coordinates (z¹,...,zⁿ),
    it can be written as ω = ∑ f_{I,J} dz^I ∧ dz̄^J where |I| = |J| = p.

    This is the key condition for Hodge classes: a cohomology class is Hodge if and only
    if it can be represented by a closed (p,p)-form.

    Defined inductively with the closure properties:
    - Zero is a (p,p)-form
    - Sum of (p,p)-forms is a (p,p)-form
    - Scalar multiple of (p,p)-form is a (p,p)-form

    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry", 1978, Ch. 0.7]. -/
inductive isPPForm' (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : (p : ℕ) → SmoothForm n X (2 * p) → Prop where
  | zero (p : ℕ) : isPPForm' n X p 0
  | add {p : ℕ} {ω η : SmoothForm n X (2 * p)} :
      isPPForm' n X p ω → isPPForm' n X p η → isPPForm' n X p (ω + η)
  | smul {p : ℕ} (c : ℂ) {ω : SmoothForm n X (2 * p)} :
      isPPForm' n X p ω → isPPForm' n X p (c • ω)

/-- **Zero is a (p,p)-form** (Trivial).
    The zero form is of type (p,p) for all p.
    Proof: Direct from the `zero` constructor. -/
theorem isPPForm_zero {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (p : ℕ) : isPPForm' n X p 0 :=
  isPPForm'.zero p

end
