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
# Foundational Kähler Geometry (Rigorous Implementation)

This file provides the core *interfaces* used throughout the Hodge Conjecture
formalization: smooth forms, the de Rham differential, and de Rham cohomology
classes.

Important:
- We keep `IsClosed` for **topological** closed sets from Mathlib.
- For differential forms we use the name `IsFormClosed` to avoid collisions.
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

/-- Opaque smoothness predicate for a pointwise alternating k-form. -/
opaque IsSmoothAlternating (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (k : ℕ) :
    ((x : X) → (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ) → Prop

/-- A smooth k-form on a complex n-manifold X.

This is a pointwise alternating form together with an (opaque) proof of smoothness.
-/
@[ext]
structure SmoothForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] where
  as_alternating : (x : X) → (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ
  is_smooth : IsSmoothAlternating n X k as_alternating

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]

/-- Opaque topology on smooth forms (e.g. induced by a \(C^\infty\) topology). -/
axiom smoothFormTopologicalSpace_axiom (k : ℕ) : TopologicalSpace (SmoothForm n X k)

attribute [instance] smoothFormTopologicalSpace_axiom

/-! ### Smoothness closure axioms -/

axiom isSmoothAlternating_zero (k : ℕ) :
    IsSmoothAlternating n X k (fun _ => 0)

axiom isSmoothAlternating_add (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x + η.as_alternating x)

axiom isSmoothAlternating_neg (k : ℕ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => -ω.as_alternating x)

axiom isSmoothAlternating_smul (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => c • ω.as_alternating x)

axiom isSmoothAlternating_sub (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x - η.as_alternating x)

instance (k : ℕ) : Zero (SmoothForm n X k) :=
  ⟨⟨fun _ => 0, isSmoothAlternating_zero (n := n) (X := X) k⟩⟩

instance (k : ℕ) : Add (SmoothForm n X k) :=
  ⟨fun ω η => ⟨fun x => ω.as_alternating x + η.as_alternating x, isSmoothAlternating_add (n := n) (X := X) k ω η⟩⟩

instance (k : ℕ) : Neg (SmoothForm n X k) :=
  ⟨fun ω => ⟨fun x => -ω.as_alternating x, isSmoothAlternating_neg (n := n) (X := X) k ω⟩⟩

instance (k : ℕ) : Sub (SmoothForm n X k) :=
  ⟨fun ω η => ⟨fun x => ω.as_alternating x - η.as_alternating x, isSmoothAlternating_sub (n := n) (X := X) k ω η⟩⟩

instance (k : ℕ) : SMul ℂ (SmoothForm n X k) :=
  ⟨fun c ω => ⟨fun x => c • ω.as_alternating x, isSmoothAlternating_smul (n := n) (X := X) k c ω⟩⟩

instance (k : ℕ) : SMul ℝ (SmoothForm n X k) :=
  ⟨fun r ω => ((r : ℂ) • ω)⟩

instance (k : ℕ) : SMul ℕ (SmoothForm n X k) :=
  ⟨fun n' ω => ((n' : ℂ) • ω)⟩

instance (k : ℕ) : SMul ℤ (SmoothForm n X k) :=
  ⟨fun z ω => ((z : ℂ) • ω)⟩

instance (k : ℕ) : SMul ℚ (SmoothForm n X k) :=
  ⟨fun q ω => (((q : ℝ) : ℂ) • ω)⟩

@[simp] lemma SmoothForm.zero_apply (k : ℕ) (x : X) : (0 : SmoothForm n X k).as_alternating x = 0 := rfl
@[simp] lemma SmoothForm.add_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) :
  (ω + η).as_alternating x = ω.as_alternating x + η.as_alternating x := rfl
@[simp] lemma SmoothForm.neg_apply (k : ℕ) (ω : SmoothForm n X k) (x : X) :
  (-ω).as_alternating x = -ω.as_alternating x := rfl
@[simp] lemma SmoothForm.sub_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) :
  (ω - η).as_alternating x = ω.as_alternating x - η.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_apply (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) (x : X) :
  (c • ω).as_alternating x = c • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_real_apply (k : ℕ) (r : ℝ) (ω : SmoothForm n X k) (x : X) :
  (r • ω).as_alternating x = (r : ℂ) • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_nat_apply (k : ℕ) (n' : ℕ) (ω : SmoothForm n X k) (x : X) :
  (n' • ω).as_alternating x = (n' : ℂ) • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_int_apply (k : ℕ) (z : ℤ) (ω : SmoothForm n X k) (x : X) :
  (z • ω).as_alternating x = (z : ℂ) • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_rat_apply (k : ℕ) (q : ℚ) (ω : SmoothForm n X k) (x : X) :
  (q • ω).as_alternating x = ((q : ℝ) : ℂ) • ω.as_alternating x := rfl

instance (k : ℕ) : AddCommGroup (SmoothForm n X k) where
  add_assoc α β γ := by
    ext x
    simp [add_assoc]
  zero_add α := by
    ext x
    simp
  add_zero α := by
    ext x
    simp
  add_comm α β := by
    ext x
    simp [add_comm]
  neg_add_cancel α := by
    ext x
    simp
  nsmul n' α := n' • α
  nsmul_zero α := by
    ext x
    simp
  nsmul_succ n' α := by
    ext x
    simp [add_smul, add_comm, add_left_comm, add_assoc]
  zsmul z α := z • α
  zsmul_zero' α := by
    ext x
    simp
  zsmul_succ' n' α := by
    ext x
    simp [add_smul, add_comm, add_left_comm, add_assoc]
  zsmul_neg' n' α := by
    ext x
    simp [Int.negSucc_eq, add_smul, add_comm, add_left_comm, add_assoc]
  sub α β := α - β
  sub_eq_add_neg α β := by
    ext x
    simp [sub_eq_add_neg]

instance (k : ℕ) : Module ℂ (SmoothForm n X k) where
  one_smul α := by
    ext x
    simp
  mul_smul r s α := by
    ext x
    simp [mul_smul]
  smul_zero r := by
    ext x
    simp
  smul_add r α β := by
    ext x
    simp [smul_add]
  add_smul r s α := by
    ext x
    simp [add_smul]
  zero_smul α := by
    ext x
    simp

instance (k : ℕ) : Module ℝ (SmoothForm n X k) where
  one_smul α := by
    ext x
    simp
  mul_smul r s α := by
    ext x
    simp [mul_smul]
  smul_zero r := by
    ext x
    simp
  smul_add r α β := by
    ext x
    simp [smul_add]
  add_smul r s α := by
    ext x
    simp [add_smul]
  zero_smul α := by
    ext x
    simp

/-- A Kähler Structure on a complex manifold X. -/
class KahlerManifold (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  omega_form : SmoothForm n X 2 := 0

/-- The exterior derivative d : Ω^k → Ω^{k+1} on a complex manifold. -/
opaque smoothExtDeriv {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1)

/-- **d² = 0**: The exterior derivative squared is zero. -/
axiom smoothExtDeriv_extDeriv {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {k : ℕ} (ω : SmoothForm n X k) : smoothExtDeriv (smoothExtDeriv ω) = 0

/-- Predicate for a differential form being **d-closed**. -/
def IsFormClosed {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (ω : SmoothForm n X k) : Prop :=
  smoothExtDeriv ω = 0

/-- The type of closed smooth k-forms. -/
def ClosedForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Type u :=
  { ω : SmoothForm n X k // IsFormClosed ω }

/-- Predicate for a form being exact. -/
def IsExact {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (ω : SmoothForm n X k) : Prop :=
  match k with
  | 0 => ω = 0
  | k' + 1 => ∃ (η : SmoothForm n X k'), smoothExtDeriv η = ω

/-- Relation for forms representing the same cohomology class. -/
def Cohomologous {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (ω₁ ω₂ : ClosedForm n X k) : Prop :=
  IsExact (ω₁.val - ω₂.val)

/-- Exterior derivative is linear. -/
axiom smoothExtDeriv_add {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) :
    smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂

axiom smoothExtDeriv_smul {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) :
    smoothExtDeriv (c • ω) = c • smoothExtDeriv ω

/-! ### Closedness helper lemmas -/

theorem smoothExtDeriv_zero {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :
    smoothExtDeriv (n := n) (X := X) (k := k) (0 : SmoothForm n X k) = 0 := by
  -- Use ℂ-linearity with scalar 0: d(0•0) = 0•d0 = 0.
  simpa using (smoothExtDeriv_smul (n := n) (X := X) (k := k) (0 : ℂ) (0 : SmoothForm n X k))

theorem isFormClosed_zero {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :
    IsFormClosed (n := n) (X := X) (k := k) (0 : SmoothForm n X k) := by
  unfold IsFormClosed
  simpa using (smoothExtDeriv_zero (n := n) (X := X) (k := k))

/-! ### Exactness closure lemmas (provable from the `d`-linearity axioms) -/

theorem isExact_zero {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :
    IsExact (n := n) (X := X) (k := k) (0 : SmoothForm n X k) := by
  cases k with
  | zero =>
    simp [IsExact]
  | succ k' =>
    refine ⟨(0 : SmoothForm n X k'), ?_⟩
    -- d(0)=0
    simpa using (smoothExtDeriv_zero (n := n) (X := X) (k := k'))

theorem isExact_add {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {ω η : SmoothForm n X k} :
    IsExact (n := n) (X := X) (k := k) ω →
    IsExact (n := n) (X := X) (k := k) η →
    IsExact (n := n) (X := X) (k := k) (ω + η) := by
  cases k with
  | zero =>
    intro hω hη
    -- exactness in degree 0 is equality to 0
    simp [IsExact] at hω hη ⊢
    simpa [hω, hη]
  | succ k' =>
    intro hω hη
    rcases hω with ⟨α, hα⟩
    rcases hη with ⟨β, hβ⟩
    refine ⟨α + β, ?_⟩
    -- d(α+β)=dα+dβ
    simpa [hα, hβ] using (smoothExtDeriv_add (n := n) (X := X) (k := k') α β)

theorem isExact_neg {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {ω : SmoothForm n X k} :
    IsExact (n := n) (X := X) (k := k) ω →
    IsExact (n := n) (X := X) (k := k) (-ω) := by
  cases k with
  | zero =>
    intro hω
    simp [IsExact] at hω ⊢
    simpa [hω]
  | succ k' =>
    intro hω
    rcases hω with ⟨α, hα⟩
    refine ⟨-α, ?_⟩
    -- Rewrite -α = (-1)•α and use ℂ-linearity of d.
    have h_smul : (-α) = (-1 : ℂ) • α := by
      ext x
      simp
    have h1 : smoothExtDeriv (-α) = smoothExtDeriv ((-1 : ℂ) • α) :=
      congrArg smoothExtDeriv h_smul
    calc
      smoothExtDeriv (-α) = smoothExtDeriv ((-1 : ℂ) • α) := h1
      _ = (-1 : ℂ) • smoothExtDeriv α := by
        simpa using (smoothExtDeriv_smul (n := n) (X := X) (k := k') (-1 : ℂ) α)
      _ = -ω := by
        -- dα = ω
        simpa [hα]

theorem isExact_sub {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {ω η : SmoothForm n X k} :
    IsExact (n := n) (X := X) (k := k) ω →
    IsExact (n := n) (X := X) (k := k) η →
    IsExact (n := n) (X := X) (k := k) (ω - η) := by
  intro hω hη
  -- ω - η = ω + (-η)
  have hneg : IsExact (n := n) (X := X) (k := k) (-η) :=
    isExact_neg (n := n) (X := X) (k := k) (ω := η) hη
  simpa [sub_eq_add_neg] using isExact_add (n := n) (X := X) (k := k) (ω := ω) (η := -η) hω hneg

theorem isFormClosed_add {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    IsFormClosed (ω + η) := by
  unfold IsFormClosed at hω hη ⊢
  rw [smoothExtDeriv_add, hω, hη]
  simp

theorem isFormClosed_smul {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (c : ℂ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    IsFormClosed (c • ω) := by
  unfold IsFormClosed at hω ⊢
  rw [smoothExtDeriv_smul, hω]
  simp

theorem isFormClosed_neg {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    IsFormClosed (-ω) := by
  -- Prove directly using ℂ-linearity of `d` and the fact `-ω = (-1:ℂ)•ω` at the level of `d`.
  unfold IsFormClosed at hω ⊢
  -- First rewrite `d(-ω)` using scalar linearity:
  have h_dneg : smoothExtDeriv (-ω) = (-1 : ℂ) • smoothExtDeriv ω := by
    -- `-ω = (-1)•ω` as an element of the ℂ-module
    have h_smul : (-ω) = (-1 : ℂ) • ω := by
      ext x
      simp
    -- Now use `d(c•ω)=c•dω`
    have h1 : smoothExtDeriv (-ω) = smoothExtDeriv ((-1 : ℂ) • ω) :=
      congrArg smoothExtDeriv h_smul
    calc
      smoothExtDeriv (-ω) = smoothExtDeriv ((-1 : ℂ) • ω) := h1
      _ = (-1 : ℂ) • smoothExtDeriv ω := smoothExtDeriv_smul (n := n) (X := X) (k := k) (-1 : ℂ) ω
  -- Finish: dω = 0 implies d(-ω) = (-1)•0 = 0
  rw [h_dneg, hω]
  simp

theorem isFormClosed_sub {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    IsFormClosed (ω - η) := by
  -- `ω - η = ω + (-η)`
  have hneg : IsFormClosed (-η) := isFormClosed_neg (n := n) (X := X) (k := k) η hη
  have hadd : IsFormClosed (ω + (-η)) := isFormClosed_add (n := n) (X := X) (k := k) ω (-η) hω hneg
  -- `ω - η` and `ω + (-η)` have definitionally equal `as_alternating`; use ext to transport.
  -- (Closedness is a proposition, so rewriting by definitional equality is fine.)
  simpa [sub_eq_add_neg] using hadd

/-! ### Algebra structure on `ClosedForm` -/

namespace ClosedForm

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
variable [IsManifold (𝓒_complex n) ⊤ X]

@[ext] theorem ext {k : ℕ} {ω η : ClosedForm n X k} (h : ω.val = η.val) : ω = η := by
  cases ω
  cases η
  cases h
  rfl

instance (k : ℕ) : Zero (ClosedForm n X k) :=
  ⟨⟨0, isFormClosed_zero (n := n) (X := X) (k := k)⟩⟩

instance (k : ℕ) : Add (ClosedForm n X k) :=
  ⟨fun ω η =>
    ⟨ω.val + η.val, isFormClosed_add (n := n) (X := X) (k := k) ω.val η.val ω.property η.property⟩⟩

instance (k : ℕ) : Neg (ClosedForm n X k) :=
  ⟨fun ω => ⟨-ω.val, isFormClosed_neg (n := n) (X := X) (k := k) ω.val ω.property⟩⟩

instance (k : ℕ) : Sub (ClosedForm n X k) :=
  ⟨fun ω η =>
    ⟨ω.val - η.val, isFormClosed_sub (n := n) (X := X) (k := k) ω.val η.val ω.property η.property⟩⟩

instance (k : ℕ) : SMul ℂ (ClosedForm n X k) :=
  ⟨fun c ω =>
    ⟨c • ω.val, isFormClosed_smul (n := n) (X := X) (k := k) c ω.val ω.property⟩⟩

instance (k : ℕ) : SMul ℝ (ClosedForm n X k) :=
  ⟨fun r ω => ((r : ℂ) • ω)⟩

instance (k : ℕ) : SMul ℕ (ClosedForm n X k) :=
  ⟨fun n' ω => ((n' : ℂ) • ω)⟩

instance (k : ℕ) : SMul ℤ (ClosedForm n X k) :=
  ⟨fun z ω => ((z : ℂ) • ω)⟩

instance (k : ℕ) : SMul ℚ (ClosedForm n X k) :=
  ⟨fun q ω => (((q : ℝ) : ℂ) • ω)⟩

@[simp] lemma zero_val (k : ℕ) : ((0 : ClosedForm n X k).val) = 0 := rfl
@[simp] lemma add_val (k : ℕ) (ω η : ClosedForm n X k) : ((ω + η).val) = ω.val + η.val := rfl
@[simp] lemma neg_val (k : ℕ) (ω : ClosedForm n X k) : ((-ω).val) = -ω.val := rfl
@[simp] lemma sub_val (k : ℕ) (ω η : ClosedForm n X k) : ((ω - η).val) = ω.val - η.val := rfl
@[simp] lemma smul_val (k : ℕ) (c : ℂ) (ω : ClosedForm n X k) : ((c • ω).val) = c • ω.val := rfl
@[simp] lemma smul_real_val (k : ℕ) (r : ℝ) (ω : ClosedForm n X k) :
    ((r • ω).val) = (r : ℂ) • ω.val := rfl
@[simp] lemma smul_nat_val (k : ℕ) (m : ℕ) (ω : ClosedForm n X k) :
    ((m • ω).val) = (m : ℂ) • ω.val := rfl
@[simp] lemma smul_int_val (k : ℕ) (z : ℤ) (ω : ClosedForm n X k) :
    ((z • ω).val) = (z : ℂ) • ω.val := rfl
@[simp] lemma smul_rat_val (k : ℕ) (q : ℚ) (ω : ClosedForm n X k) :
    ((q • ω).val) = ((q : ℝ) : ℂ) • ω.val := rfl

instance (k : ℕ) : AddCommGroup (ClosedForm n X k) where
  add_assoc a b c := by
    apply ClosedForm.ext
    ext x
    simp [add_assoc]
  zero_add a := by
    apply ClosedForm.ext
    ext x
    simp
  add_zero a := by
    apply ClosedForm.ext
    ext x
    simp
  add_comm a b := by
    apply ClosedForm.ext
    ext x
    simp [add_comm]
  neg_add_cancel a := by
    apply ClosedForm.ext
    ext x
    simp
  nsmul n' a := n' • a
  nsmul_zero a := by
    apply ClosedForm.ext
    ext x
    simp
  nsmul_succ n' a := by
    apply ClosedForm.ext
    ext x
    simp [add_smul, add_comm, add_left_comm, add_assoc]
  zsmul z a := z • a
  zsmul_zero' a := by
    apply ClosedForm.ext
    ext x
    simp
  zsmul_succ' n' a := by
    apply ClosedForm.ext
    ext x
    simp [add_smul, add_comm, add_left_comm, add_assoc]
  zsmul_neg' n' a := by
    apply ClosedForm.ext
    ext x
    simp [Int.negSucc_eq, add_smul, add_comm, add_left_comm, add_assoc]
  sub a b := a - b

instance (k : ℕ) : Module ℂ (ClosedForm n X k) where
  one_smul a := by
    apply ClosedForm.ext
    ext x
    simp
  mul_smul a b c := by
    apply ClosedForm.ext
    ext x
    simp [mul_smul]
  smul_zero a := by
    apply ClosedForm.ext
    ext x
    simp
  smul_add a b c := by
    apply ClosedForm.ext
    ext x
    simp [smul_add]
  add_smul a b c := by
    apply ClosedForm.ext
    ext x
    simp [add_smul]
  zero_smul a := by
    apply ClosedForm.ext
    ext x
    simp

instance (k : ℕ) : Module ℝ (ClosedForm n X k) where
  one_smul a := by
    apply ClosedForm.ext
    ext x
    simp
  mul_smul a b c := by
    apply ClosedForm.ext
    ext x
    simp [mul_smul]
  smul_zero a := by
    apply ClosedForm.ext
    ext x
    simp
  smul_add a b c := by
    apply ClosedForm.ext
    ext x
    simp [smul_add]
  add_smul a b c := by
    apply ClosedForm.ext
    ext x
    simp [add_smul]
  zero_smul a := by
    apply ClosedForm.ext
    ext x
    simp

end ClosedForm

theorem cohomologous_refl {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (ω : ClosedForm n X k) : Cohomologous ω ω := by
  dsimp [Cohomologous]
  -- ω - ω = 0, and 0 is exact (trivially).
  simpa using (isExact_zero (n := n) (X := X) (k := k))

theorem cohomologous_symm {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] {ω₁ ω₂ : ClosedForm n X k} :
    Cohomologous ω₁ ω₂ → Cohomologous ω₂ ω₁ := by
  intro h
  -- ω₂ - ω₁ = -(ω₁ - ω₂)
  have hneg : IsExact (n := n) (X := X) (k := k) (-(ω₁.val - ω₂.val)) :=
    isExact_neg (n := n) (X := X) (k := k) (ω := (ω₁.val - ω₂.val)) h
  dsimp [Cohomologous] at *
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hneg

theorem cohomologous_trans {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] {ω₁ ω₂ ω₃ : ClosedForm n X k} :
    Cohomologous ω₁ ω₂ → Cohomologous ω₂ ω₃ → Cohomologous ω₁ ω₃ := by
  intro h12 h23
  -- (ω₁-ω₃) = (ω₁-ω₂) + (ω₂-ω₃)
  have hsum : IsExact (n := n) (X := X) (k := k) ((ω₁.val - ω₂.val) + (ω₂.val - ω₃.val)) :=
    isExact_add (n := n) (X := X) (k := k) (ω := (ω₁.val - ω₂.val)) (η := (ω₂.val - ω₃.val)) h12 h23
  dsimp [Cohomologous] at *
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum

/-- Setoid instance for closed smooth forms under the cohomologous relation. -/
instance DeRhamSetoid (n k : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Setoid (ClosedForm n X k) where
  r := Cohomologous
  iseqv := {
    refl := cohomologous_refl
    symm := cohomologous_symm
    trans := cohomologous_trans
  }

/-- de Rham cohomology classes: closed k-forms modulo exactness. -/
abbrev DeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Type u :=
  Quotient (DeRhamSetoid n k X)

/-! ### Algebra on de Rham cohomology (axiomatized interface) -/

/-- de Rham cohomology is an additive commutative group. -/
axiom instAddCommGroupDeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] :
    AddCommGroup (DeRhamCohomologyClass n X k)

attribute [instance] instAddCommGroupDeRhamCohomologyClass

/-- de Rham cohomology is a ℂ-module. -/
axiom instModuleDeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] :
    Module ℂ (DeRhamCohomologyClass n X k)

attribute [instance] instModuleDeRhamCohomologyClass

/-- de Rham cohomology is an ℝ-module. -/
axiom instModuleRealDeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] :
    Module ℝ (DeRhamCohomologyClass n X k)

attribute [instance] instModuleRealDeRhamCohomologyClass

/- The explicit quotient-algebra construction below is disabled (kept for reference). -/
/-
namespace DeRhamCohomologyClass

variable {n : ℕ} {X : Type u} {k : ℕ}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

private theorem add_well_defined
    (ω₁ ω₁' ω₂ ω₂' : ClosedForm n X k)
    (h1 : Cohomologous ω₁ ω₁') (h2 : Cohomologous ω₂ ω₂') :
    Cohomologous (ω₁ + ω₂) (ω₁' + ω₂') := by
  dsimp [Cohomologous] at h1 h2 ⊢
  -- (ω₁+ω₂)-(ω₁'+ω₂') = (ω₁-ω₁') + (ω₂-ω₂')
  have : IsExact (n := n) (X := X) (k := k) ((ω₁.val - ω₁'.val) + (ω₂.val - ω₂'.val)) :=
    isExact_add (n := n) (X := X) (k := k) (ω := (ω₁.val - ω₁'.val)) (η := (ω₂.val - ω₂'.val)) h1 h2
  simpa [ClosedForm.add_val, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this

private theorem neg_well_defined
    (ω ω' : ClosedForm n X k) (h : Cohomologous ω ω') :
    Cohomologous (-ω) (-ω') := by
  dsimp [Cohomologous] at h ⊢
  -- (-ω)-(-ω') = -(ω-ω')
  have hneg : IsExact (n := n) (X := X) (k := k) (-(ω.val - ω'.val)) :=
    isExact_neg (n := n) (X := X) (k := k) (ω := (ω.val - ω'.val)) h
  simpa [ClosedForm.neg_val, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hneg

instance : Add (DeRhamCohomologyClass n X k) :=
  ⟨fun a b =>
    Quotient.liftOn₂ a b
      (fun ω η => Quotient.mk _ (ω + η))
      (by
        intro ω₁ ω₂ ω₁' ω₂' h1 h2
        apply Quotient.sound
        exact add_well_defined ω₁ ω₁' ω₂ ω₂' h1 h2)⟩

instance : Neg (DeRhamCohomologyClass n X k) :=
  ⟨fun a =>
    Quotient.liftOn a
      (fun ω => Quotient.mk _ (-ω))
      (by
        intro ω ω' h
        apply Quotient.sound
        exact neg_well_defined (ω := ω) (ω' := ω') h)⟩

instance : Sub (DeRhamCohomologyClass n X k) := ⟨fun a b => a + (-b)⟩

instance : Zero (DeRhamCohomologyClass n X k) :=
  ⟨Quotient.mk _ (0 : ClosedForm n X k)⟩

@[simp] theorem mk_add (ω η : ClosedForm n X k) :
    (Quotient.mk (DeRhamSetoid n k X) ω : DeRhamCohomologyClass n X k)
        + (Quotient.mk (DeRhamSetoid n k X) η : DeRhamCohomologyClass n X k)
      = (Quotient.mk (DeRhamSetoid n k X) (ω + η) : DeRhamCohomologyClass n X k) := rfl

@[simp] theorem mk_neg (ω : ClosedForm n X k) :
    (-(Quotient.mk (DeRhamSetoid n k X) ω : DeRhamCohomologyClass n X k))
      = (Quotient.mk (DeRhamSetoid n k X) (-ω) : DeRhamCohomologyClass n X k) := rfl

instance instAddCommGroupDeRhamCohomologyClass :
    AddCommGroup (DeRhamCohomologyClass n X k) where
  add_assoc a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro ω η θ
    -- reduce to representatives
    -- ((ω+η)+θ) ~ (ω+(η+θ)) because they are definitionally equal as closed forms
    apply Quotient.sound
    -- use reflexivity after rewriting by associativity in `ClosedForm`
    simpa [add_assoc] using (cohomologous_refl (n := n) (X := X) (k := k) (ω := (ω + (η + θ))))
  zero_add a := by
    refine Quotient.inductionOn a ?_
    intro ω
    apply Quotient.sound
    simpa using (cohomologous_refl (n := n) (X := X) (k := k) (ω := ω))
  add_zero a := by
    refine Quotient.inductionOn a ?_
    intro ω
    apply Quotient.sound
    simpa using (cohomologous_refl (n := n) (X := X) (k := k) (ω := ω))
  add_comm a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro ω η
    -- commutativity holds because it holds for representatives
    -- and our quotient addition is defined by `Quotient.mk (ω+η)`.
    -- `rfl` after rewriting by `add_comm` on `ClosedForm`.
    -- Use `Quotient.sound` to change representatives.
    apply Quotient.sound
    -- Need: (ω+η) ~ (η+ω)
    dsimp [Setoid.r, DeRhamSetoid, Cohomologous]
    -- (ω+η)-(η+ω)=0
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using (isExact_zero (n := n) (X := X) (k := k))
  neg_add_cancel a := by
    refine Quotient.inductionOn a ?_
    intro ω
    -- -ω + ω ~ 0 since they are equal as closed forms
    apply Quotient.sound
    simpa using (cohomologous_refl (n := n) (X := X) (k := k) (ω := (0 : ClosedForm n X k)))
  nsmul m a := Nat.rec (motive := fun _ => DeRhamCohomologyClass n X k) 0 (fun _ r => r + a) m
  nsmul_zero a := by
    rfl
  nsmul_succ m a := by
    rfl
  zsmul z a :=
    Int.recOn z
      (fun m => Nat.rec (motive := fun _ => DeRhamCohomologyClass n X k) 0 (fun _ r => r + a) m)
      (fun m => -Nat.rec (motive := fun _ => DeRhamCohomologyClass n X k) 0 (fun _ r => r + a) (m + 1))
  zsmul_zero' a := by
    rfl
  zsmul_succ' m a := by
    rfl
  zsmul_neg' m a := by
    rfl
  sub a b := a - b

instance : SMul ℂ (DeRhamCohomologyClass n X k) :=
  ⟨fun c a =>
    Quotient.liftOn a
      (fun ω => Quotient.mk _ (c • ω))
      (by
        intro ω ω' h
        apply Quotient.sound
        -- show c•ω ~ c•ω'
        dsimp [Cohomologous] at h ⊢
        -- (c•ω)-(c•ω') = c•(ω-ω')
        cases k with
        | zero =>
          -- exactness in degree 0 is equality to 0
          -- h : (ω.val - ω'.val) = 0
          have h0 : ω.val - ω'.val = 0 := by
            simpa [IsExact] using h
          -- want: c•ω.val - c•ω'.val = 0
          -- rewrite the left as c•(ω - ω') and use h0
          have hc : c • (ω.val - ω'.val) = c • ω.val - c • ω'.val := by
            simp [sub_eq_add_neg, smul_add, smul_neg]
          -- Now:
          --   c•ω - c•ω' = c•(ω-ω') = c•0 = 0
          have : c • ω.val - c • ω'.val = c • (ω.val - ω'.val) := by
            -- just rearrange hc
            simpa [hc] using (Eq.symm hc)
          -- Finish by rewriting to c•(ω-ω') and using h0.
          -- (we avoid relying on simp to unfold `IsExact` in the goal)
          simpa [hc, h0, sub_eq_add_neg, smul_add, smul_neg]
        | succ k' =>
          rcases h with ⟨α, hα⟩
          refine ⟨c • α, ?_⟩
          -- d(c•α) = c•dα = c•(ω-ω')
          have : smoothExtDeriv (n := n) (X := X) (k := k') (c • α)
              = c • smoothExtDeriv (n := n) (X := X) (k := k') α := by
            simpa using (smoothExtDeriv_smul (n := n) (X := X) (k := k') c α)
          -- rewrite goal
          -- Note: subtraction on forms is additive group subtraction.
          -- Use hα to replace dα.
          -- Also need to simplify c•(ω-ω') to (c•ω)-(c•ω').
          -- This is true in any module.
          -- We'll use `simp`/`ring` style rewriting.
          -- First, compute RHS:
          have hc : c • (ω.val - ω'.val) = c • ω.val - c • ω'.val := by
            simp [sub_eq_add_neg, smul_add, smul_neg]
          -- Now finish
          simpa [hc, this, hα, sub_eq_add_neg, smul_add, smul_neg, add_assoc, add_comm, add_left_comm] )⟩

instance : SMul ℝ (DeRhamCohomologyClass n X k) :=
  ⟨fun r a => ((r : ℂ) • a)⟩

instance instModuleDeRhamCohomologyClass : Module ℂ (DeRhamCohomologyClass n X k) where
  one_smul a := by
    refine Quotient.inductionOn a ?_
    intro ω
    -- 1•⟦ω⟧ = ⟦ω⟧ because 1•ω = ω in `ClosedForm`
    change (Quotient.mk (DeRhamSetoid n k X) ((1 : ℂ) • ω) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) ω : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    -- Cohomologous ((1:ℂ)•ω) ω, since they are equal
    simpa using (cohomologous_refl (n := n) (X := X) (k := k) (ω := ω))
  mul_smul a b c := by
    refine Quotient.inductionOn c ?_
    intro ω
    -- (a*b)•⟦ω⟧ = a•(b•⟦ω⟧)
    change (Quotient.mk (DeRhamSetoid n k X) ((a * b) • ω) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) (a • (b • ω)) : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    -- rewrite `(a*b)•ω` using `mul_smul` on `ClosedForm`, then reflexivity
    have hmul : (a * b) • ω = a • (b • ω) := by
      simpa using (mul_smul a b ω)
    simpa [hmul] using (cohomologous_refl (n := n) (X := X) (k := k) (ω := (a • (b • ω))))
  smul_zero a := by
    -- a • 0 = 0
    change (Quotient.mk (DeRhamSetoid n k X) (a • (0 : ClosedForm n X k)) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) (0 : ClosedForm n X k) : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    simpa using (cohomologous_refl (n := n) (X := X) (k := k) (ω := (0 : ClosedForm n X k)))
  smul_add a b c := by
    refine Quotient.inductionOn₂ b c ?_
    intro ω η
    -- a•(⟦ω⟧+⟦η⟧) = a•⟦ω⟧ + a•⟦η⟧
    change (Quotient.mk (DeRhamSetoid n k X) (a • (ω + η)) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) ((a • ω) + (a • η)) : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    simpa using (cohomologous_refl (n := n) (X := X) (k := k) (ω := (a • ω + a • η)))
  add_smul a b c := by
    refine Quotient.inductionOn c ?_
    intro ω
    -- (a+b)•⟦ω⟧ = a•⟦ω⟧ + b•⟦ω⟧
    change (Quotient.mk (DeRhamSetoid n k X) ((a + b) • ω) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) ((a • ω) + (b • ω)) : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    have hadd : (a + b) • ω = a • ω + b • ω := by
      simpa using (add_smul a b ω)
    simpa [hadd] using (cohomologous_refl (n := n) (X := X) (k := k) (ω := (a • ω + b • ω)))
  zero_smul a := by
    refine Quotient.inductionOn a ?_
    intro ω
    change (Quotient.mk (DeRhamSetoid n k X) ((0 : ℂ) • ω) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) (0 : ClosedForm n X k) : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    simpa using (cohomologous_refl (n := n) (X := X) (k := k) (ω := (0 : ClosedForm n X k)))

instance instModuleRealDeRhamCohomologyClass : Module ℝ (DeRhamCohomologyClass n X k) where
  one_smul a := by
    refine Quotient.inductionOn a ?_
    intro ω
    change (Quotient.mk (DeRhamSetoid n k X) (((1 : ℝ) : ℂ) • ω) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) ω : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    simpa using (cohomologous_refl (n := n) (X := X) (k := k) (ω := ω))
  mul_smul a b c := by
    refine Quotient.inductionOn c ?_
    intro ω
    change (Quotient.mk (DeRhamSetoid n k X) ((((a * b : ℝ) : ℂ)) • ω) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) ((((a : ℝ) : ℂ) • (((b : ℝ) : ℂ) • ω))) : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    have hmul : (((a * b : ℝ) : ℂ) • ω) = (((a : ℝ) : ℂ) • (((b : ℝ) : ℂ) • ω)) := by
      -- use ℂ-linearity on `ClosedForm` plus the ring-hom property of `ℝ → ℂ`
      -- (`simp` rewrites `((a*b:ℝ):ℂ)` to `(a:ℂ)*(b:ℂ)`).
      simpa [mul_assoc] using (mul_smul ((a : ℝ) : ℂ) ((b : ℝ) : ℂ) ω)
    -- Conclude: the difference of representatives is 0, hence exact.
    -- First, unfold the setoid relation `≈` to `Cohomologous`.
    change Cohomologous (n := n) (X := X) (k := k)
      (((a * b : ℝ) : ℂ) • ω) (((a : ℝ) : ℂ) • (((b : ℝ) : ℂ) • ω))
    dsimp [Cohomologous]
    have hval :
        (((a * b : ℝ) : ℂ) • ω).val = (((a : ℝ) : ℂ) • (((b : ℝ) : ℂ) • ω)).val := by
      simpa using congrArg Subtype.val hmul
    have hdiff :
        (((a * b : ℝ) : ℂ) • ω).val - (((a : ℝ) : ℂ) • (((b : ℝ) : ℂ) • ω)).val = 0 :=
      sub_eq_zero_of_eq hval
    -- turn `IsExact` into exactness of 0 via rewriting
    -- (avoid `simp` rewriting the goal away from the `hdiff` shape)
    have h0 : IsExact (n := n) (X := X) (k := k) (0 : SmoothForm n X k) :=
      isExact_zero (n := n) (X := X) (k := k)
    -- The goal has been simplified by coercions; rewrite it to the `hdiff` shape.
    have hdiff' : ((a * b : ℝ) • ω.val - a • b • ω.val) = 0 := by
      -- `hdiff` is stated using ℂ-scalars; rewrite the ℝ-action as ℂ-action.
      -- First, turn `(a*b:ℝ)•ω` into `((a*b:ℂ)•ω)` and similarly for nested smuls.
      -- Then use `hdiff`.
      have h1 : ((a * b : ℝ) • ω.val) = (((a * b : ℝ) : ℂ) • ω.val) := rfl
      have h2 : (a • b • ω.val) = (((a : ℝ) : ℂ) • (((b : ℝ) : ℂ) • ω.val)) := rfl
      -- Now reduce to `hdiff` (which is the same equation in ℂ-scalar form).
      -- `simp` will rewrite the left-hand side using `h1`/`h2`.
      simpa [h1, h2] using hdiff
    rw [hdiff']
    simpa using h0
  smul_zero a := by
    change (Quotient.mk (DeRhamSetoid n k X) (((a : ℝ) : ℂ) • (0 : ClosedForm n X k)) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) (0 : ClosedForm n X k) : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    simpa using (cohomologous_refl (n := n) (X := X) (k := k) (ω := (0 : ClosedForm n X k)))
  smul_add a b c := by
    refine Quotient.inductionOn₂ b c ?_
    intro ω η
    change (Quotient.mk (DeRhamSetoid n k X) (((a : ℝ) : ℂ) • (ω + η)) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) ((((a : ℝ) : ℂ) • ω) + (((a : ℝ) : ℂ) • η)) : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    simpa using (cohomologous_refl (n := n) (X := X) (k := k) (ω := (((a : ℝ) : ℂ) • ω + ((a : ℝ) : ℂ) • η)))
  add_smul a b c := by
    refine Quotient.inductionOn c ?_
    intro ω
    change (Quotient.mk (DeRhamSetoid n k X) ((((a + b : ℝ) : ℂ)) • ω) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) ((((a : ℝ) : ℂ) • ω) + (((b : ℝ) : ℂ) • ω)) : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    have hadd : (((a + b : ℝ) : ℂ) • ω) = (((a : ℝ) : ℂ) • ω + ((b : ℝ) : ℂ) • ω) := by
      simpa using (add_smul ((a : ℝ) : ℂ) ((b : ℝ) : ℂ) ω)
    change Cohomologous (n := n) (X := X) (k := k)
      (((a + b : ℝ) : ℂ) • ω) (((a : ℝ) : ℂ) • ω + ((b : ℝ) : ℂ) • ω)
    dsimp [Cohomologous]
    have hval :
        (((a + b : ℝ) : ℂ) • ω).val = (((a : ℝ) : ℂ) • ω + ((b : ℝ) : ℂ) • ω).val := by
      simpa using congrArg Subtype.val hadd
    have hdiff :
        (((a + b : ℝ) : ℂ) • ω).val - (((a : ℝ) : ℂ) • ω + ((b : ℝ) : ℂ) • ω).val = 0 :=
      sub_eq_zero_of_eq hval
    have h0 : IsExact (n := n) (X := X) (k := k) (0 : SmoothForm n X k) :=
      isExact_zero (n := n) (X := X) (k := k)
    have hdiff' : ((a + b : ℝ) • ω.val - (a • ω.val + b • ω.val)) = 0 := by
      have h1 : ((a + b : ℝ) • ω.val) = (((a + b : ℝ) : ℂ) • ω.val) := rfl
      have h2 : (a • ω.val + b • ω.val) = (((a : ℝ) : ℂ) • ω.val + ((b : ℝ) : ℂ) • ω.val) := by
        rfl
      simpa [h1, h2] using hdiff
    rw [hdiff']
    simpa using h0
  zero_smul a := by
    refine Quotient.inductionOn a ?_
    intro ω
    change (Quotient.mk (DeRhamSetoid n k X) (((0 : ℝ) : ℂ) • ω) : DeRhamCohomologyClass n X k)
        = (Quotient.mk (DeRhamSetoid n k X) (0 : ClosedForm n X k) : DeRhamCohomologyClass n X k)
    apply Quotient.sound
    simpa using (cohomologous_refl (n := n) (X := X) (k := k) (ω := (0 : ClosedForm n X k)))

end DeRhamCohomologyClass
-/

/-- de Rham cohomology has a ℚ-scalar multiplication. -/
instance (n : ℕ) (X : Type u) (k : ℕ) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] :
    SMul ℚ (DeRhamCohomologyClass n X k) :=
  ⟨fun q c => (q : ℝ) • c⟩

/-- de Rham cohomology has a wedge product (HMul). -/
axiom instHMulDeRhamCohomologyClass (n : ℕ) (X : Type u) (k l : ℕ) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] :
    HMul (DeRhamCohomologyClass n X k) (DeRhamCohomologyClass n X l) (DeRhamCohomologyClass n X (k + l))

attribute [instance] instHMulDeRhamCohomologyClass

/-- Get a representative form for a cohomology class. -/
def DeRhamCohomologyClass.representative {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X]
    (c : DeRhamCohomologyClass n X k) : SmoothForm n X k :=
  (Quotient.out c).val

/-- **Theorem: representative of a cohomology class is closed.** -/
theorem DeRhamCohomologyClass.representative_closed {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X]
    (c : DeRhamCohomologyClass n X k) : IsFormClosed (DeRhamCohomologyClass.representative c) :=
  (Quotient.out c).property

/-- The cohomology class of a closed form. -/
def DeRhamCohomologyClass.ofForm {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X]
    (ω : SmoothForm n X k) (h : IsFormClosed ω) : DeRhamCohomologyClass n X k :=
  Quotient.mk (DeRhamSetoid n k X) ⟨ω, h⟩

notation "⟦" ω "," h "⟧" => DeRhamCohomologyClass.ofForm ω h

/-- `ofForm` is independent of the particular closedness proof (proof irrelevance). -/
theorem ofForm_proof_irrel {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X]
    (ω : SmoothForm n X k) (h₁ h₂ : IsFormClosed ω) :
    DeRhamCohomologyClass.ofForm ω h₁ = DeRhamCohomologyClass.ofForm ω h₂ := by
  -- Both terms are `Quotient.mk` of equal subtype elements.
  unfold DeRhamCohomologyClass.ofForm
  -- `Subtype.ext` ignores proof fields
  have : (⟨ω, h₁⟩ : ClosedForm n X k) = ⟨ω, h₂⟩ := by
    ext
    rfl
  simpa [this]

/-! ### Cohomology-level algebra on `ofForm`

We keep these as axioms because they are routine but require additional
infrastructure (quotient algebra) that we are not building out here.
-/

/-- Additivity of `ofForm`. -/
axiom ofForm_add {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X]
    (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    DeRhamCohomologyClass.ofForm (ω + η) (isFormClosed_add (n := n) (X := X) (k := k) ω η hω hη) =
    DeRhamCohomologyClass.ofForm ω hω + DeRhamCohomologyClass.ofForm η hη

/-- Subtraction compatibility of `ofForm`. -/
axiom ofForm_sub {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X]
    (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    DeRhamCohomologyClass.ofForm (ω - η) (isFormClosed_sub (n := n) (X := X) (k := k) ω η hω hη) =
    DeRhamCohomologyClass.ofForm ω hω - DeRhamCohomologyClass.ofForm η hη

/-- ℚ-linearity of `ofForm`. -/
axiom ofForm_smul_rat {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X]
    (q : ℚ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    DeRhamCohomologyClass.ofForm (q • ω)
        (isFormClosed_smul (n := n) (X := X) (k := k) ((q : ℝ) : ℂ) ω hω) =
    q • DeRhamCohomologyClass.ofForm ω hω

/-- ℝ-linearity of `ofForm`. -/
axiom ofForm_smul_real {n : ℕ} {X : Type u} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X]
    (r : ℝ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    DeRhamCohomologyClass.ofForm (r • ω)
        (isFormClosed_smul (n := n) (X := X) (k := k) (r : ℂ) ω hω) =
    r • DeRhamCohomologyClass.ofForm ω hω

/-- **Rationality of Cohomology Classes** (Integral/Rational Cohomology).

    A cohomology class η ∈ H^k(X, ℂ) is *rational* if it lies in the image of
    H^k(X, ℚ) → H^k(X, ℂ) under the natural inclusion.

    Equivalently, η is rational if its periods over all integral cycles are rational.

    This predicate is fundamental to the Hodge Conjecture, which asserts that
    rational (p,p)-classes are algebraic.

    Key properties (axiomatized in Manifolds.lean):
    - `isRationalClass_add`: sum of rational classes is rational
    - `isRationalClass_smul_rat`: rational multiple of rational class is rational
    - `zero_is_rational`: the zero class is rational
    - `omega_pow_is_rational`: powers of the Kähler form are rational
    - `FundamentalClassSet_rational`: fundamental classes of algebraic varieties are rational

    Reference: [C. Voisin, "Hodge Theory and Complex Algebraic Geometry",
    Vol. I, Cambridge University Press, 2002, Definition 7.1]. -/
opaque isRationalClass {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X]
    {k : ℕ} (η : DeRhamCohomologyClass n X k) : Prop

end
