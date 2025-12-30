import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Defs.Induced
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Alternating.Basic

noncomputable section

open Classical

set_option autoImplicit false

universe u

def 𝓒_complex (n : ℕ) : ModelWithCorners ℂ (EuclideanSpace ℂ (Fin n)) (EuclideanSpace ℂ (Fin n)) :=
  modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin n))

class ProjectiveComplexManifold (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    extends IsManifold (𝓒_complex n) ⊤ X, CompactSpace X where
  embedding_dim : ℕ

opaque IsSmoothAlternating (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (k : ℕ) :
    ((x : X) → (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ) → Prop

@[ext]
structure SmoothForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] where
  as_alternating : (x : X) → (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ
  is_smooth : IsSmoothAlternating n X k as_alternating

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]

axiom smoothFormTopologicalSpace_axiom (k : ℕ) : TopologicalSpace (SmoothForm n X k)
attribute [instance] smoothFormTopologicalSpace_axiom

axiom isSmoothAlternating_zero (k : ℕ) : IsSmoothAlternating n X k (fun _ => 0)
axiom isSmoothAlternating_add (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x + η.as_alternating x)
axiom isSmoothAlternating_neg (k : ℕ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => -ω.as_alternating x)
axiom isSmoothAlternating_smul (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => c • ω.as_alternating x)
axiom isSmoothAlternating_sub (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x - η.as_alternating x)
axiom isSmoothAlternating_wedge (k l : ℕ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsSmoothAlternating n X (k + l) (fun x => (ω.as_alternating x).wedge (η.as_alternating x))

instance (k : ℕ) : Zero (SmoothForm n X k) := ⟨⟨fun _ => 0, isSmoothAlternating_zero k⟩⟩
instance (k : ℕ) : Add (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x + η.as_alternating x, isSmoothAlternating_add k ω η⟩⟩
instance (k : ℕ) : Neg (SmoothForm n X k) := ⟨fun ω => ⟨fun x => -ω.as_alternating x, isSmoothAlternating_neg k ω⟩⟩
instance (k : ℕ) : Sub (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x - η.as_alternating x, isSmoothAlternating_sub k ω η⟩⟩
instance (k : ℕ) : SMul ℂ (SmoothForm n X k) := ⟨fun c ω => ⟨fun x => c • ω.as_alternating x, isSmoothAlternating_smul k c ω⟩⟩
instance (k : ℕ) : SMul ℝ (SmoothForm n X k) := ⟨fun r ω => ((r : ℂ) • ω)⟩
instance (k : ℕ) : SMul ℕ (SmoothForm n X k) := ⟨fun n_nat ω => ((n_nat : ℂ) • ω)⟩
instance (k : ℕ) : SMul ℤ (SmoothForm n X k) := ⟨fun z ω => ((z : ℂ) • ω)⟩
instance (k : ℕ) : SMul ℚ (SmoothForm n X k) := ⟨fun q ω => (((q : ℝ) : ℂ) • ω)⟩

@[simp] lemma SmoothForm.zero_apply (k : ℕ) (x : X) : (0 : SmoothForm n X k).as_alternating x = 0 := rfl
@[simp] lemma SmoothForm.add_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) : (ω + η).as_alternating x = ω.as_alternating x + η.as_alternating x := rfl
@[simp] lemma SmoothForm.neg_apply (k : ℕ) (ω : SmoothForm n X k) (x : X) : (-ω).as_alternating x = -ω.as_alternating x := rfl
@[simp] lemma SmoothForm.sub_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) : (ω - η).as_alternating x = ω.as_alternating x - η.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_apply (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) (x : X) : (c • ω).as_alternating x = c • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_real_apply (k : ℕ) (r : ℝ) (ω : SmoothForm n X k) (x : X) : (r • ω).as_alternating x = (r : ℂ) • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_nat_apply (k : ℕ) (n_nat : ℕ) (ω : SmoothForm n X k) (x : X) : (n_nat • ω).as_alternating x = (n_nat : ℂ) • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_int_apply (k : ℕ) (z : ℤ) (ω : SmoothForm n X k) (x : X) : (z • ω).as_alternating x = (z : ℂ) • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_rat_apply (k : ℕ) (q : ℚ) (ω : SmoothForm n X k) (x : X) : (q • ω).as_alternating x = ((q : ℝ) : ℂ) • ω.as_alternating x := rfl

instance (k : ℕ) : AddCommGroup (SmoothForm n X k) where
  add_assoc α β γ := by ext x; simp [add_assoc]
  zero_add α := by ext x; simp
  add_zero α := by ext x; simp
  add_comm α β := by ext x; simp [add_comm]
  neg_add_cancel α := by ext x; simp
  nsmul n_nat α := n_nat • α
  nsmul_zero α := by ext x; simp
  nsmul_succ n_nat α := by ext x; simp [add_smul, add_comm, add_assoc]
  zsmul z α := z • α
  zsmul_zero' α := by ext x; simp
  zsmul_succ' n_nat α := by ext x; simp [add_smul, add_comm, add_assoc]
  zsmul_neg' n_nat α := by ext x; simp [Int.negSucc_eq, add_smul, add_comm, add_assoc]
  sub α β := α - β
  sub_eq_add_neg α β := by ext x; simp [sub_eq_add_neg]

instance (k : ℕ) : Module ℂ (SmoothForm n X k) where
  one_smul α := by ext x; simp
  mul_smul r s α := by ext x; simp [mul_smul]
  smul_zero r := by ext x; simp
  smul_add r α β := by ext x; simp [smul_add]
  add_smul r s α := by ext x; simp [add_smul]
  zero_smul α := by ext x; simp

instance (k : ℕ) : Module ℝ (SmoothForm n X k) where
  one_smul α := by ext x; simp
  mul_smul r s α := by ext x; simp [mul_smul]
  smul_zero r := by ext x; simp
  smul_add r α β := by ext x; simp [smul_add]
  add_smul r s α := by ext x; simp [add_smul]
  zero_smul α := by ext x; simp

class KahlerManifold (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] where
  omega_form : SmoothForm n X 2 := 0

axiom tangentNorm {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] (x : X) : Norm (TangentSpace (𝓒_complex n) x)
attribute [instance] tangentNorm
axiom tangentNormedAddCommGroup {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] (x : X) : NormedAddCommGroup (TangentSpace (𝓒_complex n) x)
attribute [instance] tangentNormedAddCommGroup
axiom tangentNormedSpace {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] (x : X) : NormedSpace ℂ (TangentSpace (𝓒_complex n) x)
attribute [instance] tangentNormedSpace
instance (x : X) : NormedSpace ℝ (TangentSpace (𝓒_complex n) x) := NormedSpace.restrictScalars ℝ ℂ _
axiom tangentFiniteDimensional {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] (x : X) : FiniteDimensional ℂ (TangentSpace (𝓒_complex n) x)
attribute [instance] tangentFiniteDimensional
instance (x : X) (k : ℕ) : Norm ((TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℂ] ℂ) := inferInstance

opaque smoothExtDeriv {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1)
axiom smoothExtDeriv_extDeriv {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] {k : ℕ} (ω : SmoothForm n X k) : smoothExtDeriv (smoothExtDeriv ω) = 0

def IsFormClosed {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] (ω : SmoothForm n X k) : Prop := smoothExtDeriv ω = 0

def ClosedForm (n : ℕ) (X : Type u) (k : ℕ) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Type u := { ω : SmoothForm n X k // IsFormClosed ω }

def IsExact {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] (ω : SmoothForm n X k) : Prop :=
  match k with
  | 0 => ω = 0
  | k_pred + 1 => ∃ (η : SmoothForm n X k_pred), smoothExtDeriv η = ω

def Cohomologous {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] (ω₁ ω₂ : ClosedForm n X k) : Prop := IsExact (ω₁.val - ω₂.val)

axiom smoothExtDeriv_add {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) : smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂
axiom smoothExtDeriv_smul {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) : smoothExtDeriv (c • ω) = c • smoothExtDeriv ω

theorem smoothExtDeriv_zero {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : smoothExtDeriv (n := n) (X := X) (k := k) (0 : SmoothForm n X k) = 0 := by
  simpa using (smoothExtDeriv_smul (n := n) (X := X) (k := k) (0 : ℂ) (0 : SmoothForm n X k))

theorem isFormClosed_zero {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : IsFormClosed (n := n) (X := X) (k := k) (0 : SmoothForm n X k) := by
  unfold IsFormClosed
  simpa using (smoothExtDeriv_zero (n := n) (X := X) (k := k))

theorem isExact_zero {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : IsExact (n := n) (X := X) (k := k) (0 : SmoothForm n X k) := by
  cases k with
  | zero => simp [IsExact]
  | succ k_pred => refine ⟨(0 : SmoothForm n X k_pred), ?_⟩; simpa using (smoothExtDeriv_zero (n := n) (X := X) (k := k_pred))

theorem isExact_add {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] {ω η : SmoothForm n X k} :
    IsExact (n := n) (X := X) (k := k) ω → IsExact (n := n) (X := X) (k := k) η → IsExact (n := n) (X := X) (k := k) (ω + η) := by
  cases k with
  | zero => intro hω hη; simp [IsExact] at hω hη ⊢; simpa [hω, hη]
  | succ k_pred => intro hω hη; rcases hω with ⟨α, hα⟩; rcases hη with ⟨β, hβ⟩; refine ⟨α + β, ?_⟩; simpa [hα, hβ] using (smoothExtDeriv_add (n := n) (X := X) (k := k_pred) α β)

theorem isExact_neg {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] {ω : SmoothForm n X k} :
    IsExact (n := n) (X := X) (k := k) ω → IsExact (n := n) (X := X) (k := k) (-ω) := by
  cases k with
  | zero => intro hω; simp [IsExact] at hω ⊢; simpa [hω]
  | succ k_pred => intro hω; rcases hω with ⟨α, hα⟩; refine ⟨-α, ?_⟩; have h_smul : (-α) = (-1 : ℂ) • α := by ext x; simp
    calc smoothExtDeriv (-α) = smoothExtDeriv ((-1 : ℂ) • α) := congrArg smoothExtDeriv h_smul
      _ = (-1 : ℂ) • smoothExtDeriv α := by simpa using (smoothExtDeriv_smul (n := n) (X := X) (k := k_pred) (-1 : ℂ) α)
      _ = -ω := by simpa [hα]

theorem isExact_sub {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] {ω η : SmoothForm n X k} :
    IsExact (n := n) (X := X) (k := k) ω → IsExact (n := n) (X := X) (k := k) η → IsExact (n := n) (X := X) (k := k) (ω - η) := by
  intro hω hη; have hneg : IsExact (n := n) (X := X) (k := k) (-η) := isExact_neg (n := n) (X := X) (k := k) (ω := η) hη
  simpa [sub_eq_add_neg] using isExact_add (n := n) (X := X) (k := k) (ω := ω) (η := -η) hω hneg

theorem isFormClosed_add {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : IsFormClosed (ω + η) := by
  unfold IsFormClosed at hω hη ⊢; rw [smoothExtDeriv_add, hω, hη]; simp

theorem isFormClosed_smul {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] (c : ℂ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : IsFormClosed (c • ω) := by
  unfold IsFormClosed at hω ⊢; rw [smoothExtDeriv_smul, hω]; simp

theorem isFormClosed_neg {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] (ω : SmoothForm n X k) (hω : IsFormClosed ω) : IsFormClosed (-ω) := by
  unfold IsFormClosed at hω ⊢; have h_smul : (-ω) = (-1 : ℂ) • ω := by ext x; simp
  calc smoothExtDeriv (-ω) = smoothExtDeriv ((-1 : ℂ) • ω) := congrArg smoothExtDeriv h_smul
    _ = (-1 : ℂ) • smoothExtDeriv ω := smoothExtDeriv_smul (n := n) (X := X) (k := k) (-1 : ℂ) ω
    _ = 0 := by simp [hω]

theorem isFormClosed_sub {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : IsFormClosed (ω - η) := by
  have hneg : IsFormClosed (-η) := isFormClosed_neg (n := n) (X := X) (k := k) η hη
  simpa [sub_eq_add_neg] using isFormClosed_add (n := n) (X := X) (k := k) ω (-η) hω hneg

namespace ClosedForm
variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
@[ext] theorem ext {k : ℕ} {ω η : ClosedForm n X k} (h : ω.val = η.val) : ω = η := by cases ω; cases η; cases h; rfl
instance (k : ℕ) : Zero (ClosedForm n X k) := ⟨⟨0, isFormClosed_zero (n := n) (X := X) (k := k)⟩⟩
instance (k : ℕ) : Add (ClosedForm n X k) := ⟨fun ω η => ⟨ω.val + η.val, isFormClosed_add (n := n) (X := X) (k := k) ω.val η.val ω.property η.property⟩⟩
instance (k : ℕ) : Neg (ClosedForm n X k) := ⟨fun ω => ⟨-ω.val, isFormClosed_neg (n := n) (X := X) (k := k) ω.val ω.property⟩⟩
instance (k : ℕ) : Sub (ClosedForm n X k) := ⟨fun ω η => ⟨ω.val - η.val, isFormClosed_sub (n := n) (X := X) (k := k) ω.val η.val ω.property η.property⟩⟩
instance (k : ℕ) : SMul ℂ (ClosedForm n X k) := ⟨fun c ω => ⟨c • ω.val, isFormClosed_smul (n := n) (X := X) (k := k) c ω.val ω.property⟩⟩
instance (k : ℕ) : SMul ℝ (ClosedForm n X k) := ⟨fun r ω => ((r : ℂ) • ω)⟩
instance (k : ℕ) : SMul ℕ (ClosedForm n X k) := ⟨fun n_nat ω => ((n_nat : ℂ) • ω)⟩
instance (k : ℕ) : SMul ℤ (ClosedForm n X k) := ⟨fun z ω => ((z : ℂ) • ω)⟩
instance (k : ℕ) : SMul ℚ (ClosedForm n X k) := ⟨fun q ω => (((q : ℝ) : ℂ) • ω)⟩
@[simp] lemma zero_val (k : ℕ) : ((0 : ClosedForm n X k).val) = 0 := rfl
@[simp] lemma add_val (k : ℕ) (ω η : ClosedForm n X k) : ((ω + η).val) = ω.val + η.val := rfl
@[simp] lemma neg_val (k : ℕ) (ω : ClosedForm n X k) : ((-ω).val) = -ω.val := rfl
@[simp] lemma sub_val (k : ℕ) (ω η : ClosedForm n X k) : ((ω - η).val) = ω.val - η.val := rfl
@[simp] lemma smul_val (k : ℕ) (c : ℂ) (ω : ClosedForm n X k) : ((c • ω).val) = c • ω.val := rfl
instance (k : ℕ) : AddCommGroup (ClosedForm n X k) where
  add_assoc a b c := by apply ClosedForm.ext; ext x; simp [add_assoc]
  zero_add a := by apply ClosedForm.ext; ext x; simp
  add_zero a := by apply ClosedForm.ext; ext x; simp
  add_comm a b := by apply ClosedForm.ext; ext x; simp [add_comm]
  neg_add_cancel a := by apply ClosedForm.ext; ext x; simp
  nsmul n_nat a := n_nat • a
  nsmul_zero a := by apply ClosedForm.ext; ext x; simp [SMul.smul, SmoothForm.smul_nat_apply, zero_val]
  nsmul_succ n_nat a := by apply ClosedForm.ext; ext x; simp [SMul.smul, SmoothForm.smul_nat_apply, add_val, add_smul, add_comm]
  zsmul z a := z • a
  zsmul_zero' a := by apply ClosedForm.ext; ext x; simp [SMul.smul, SmoothForm.smul_int_apply, zero_val]
  zsmul_succ' n_nat a := by apply ClosedForm.ext; ext x; simp [SMul.smul, SmoothForm.smul_int_apply, add_val, add_smul, add_comm]
  zsmul_neg' n_nat a := by apply ClosedForm.ext; ext x; simp [Int.negSucc_eq, SMul.smul, SmoothForm.smul_int_apply, add_val, add_smul, add_comm]
  sub a b := a - b
  sub_eq_add_neg a b := by apply ClosedForm.ext; ext x; simp [sub_eq_add_neg]
instance (k : ℕ) : Module ℂ (ClosedForm n X k) where
  one_smul a := by apply ClosedForm.ext; ext x; simp
  mul_smul a b c := by apply ClosedForm.ext; ext x; simp [mul_smul]
  smul_zero a := by apply ClosedForm.ext; ext x; simp
  smul_add a b c := by apply ClosedForm.ext; ext x; simp [smul_add]
  add_smul a b c := by apply ClosedForm.ext; ext x; simp [add_smul]
  zero_smul a := by apply ClosedForm.ext; ext x; simp
instance (k : ℕ) : Module ℝ (ClosedForm n X k) where
  one_smul a := by apply ClosedForm.ext; ext x; simp
  mul_smul a b c := by apply ClosedForm.ext; ext x; simp [mul_smul]
  smul_zero a := by apply ClosedForm.ext; ext x; simp
  smul_add a b c := by apply ClosedForm.ext; ext x; simp [smul_add]
  add_smul a b c := by apply ClosedForm.ext; ext x; simp [add_smul]
  zero_smul a := by apply ClosedForm.ext; ext x; simp
end ClosedForm

theorem cohomologous_refl {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] (ω : ClosedForm n X k) : Cohomologous ω ω := by
  dsimp [Cohomologous]; simpa using (isExact_zero (n := n) (X := X) (k := k))
theorem cohomologous_symm {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] {ω₁ ω₂ : ClosedForm n X k} :
    Cohomologous ω₁ ω₂ → Cohomologous ω₂ ω₁ := by
  intro h; have hneg : IsExact (n := n) (X := X) (k := k) (-(ω₁.val - ω₂.val)) := isExact_neg (n := n) (X := X) (k := k) (ω := (ω₁.val - ω₂.val)) h
  dsimp [Cohomologous] at *; simpa [sub_eq_add_neg, add_assoc, add_comm] using hneg
theorem cohomologous_trans {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] {ω₁ ω₂ ω₃ : ClosedForm n X k} :
    Cohomologous ω₁ ω₂ → Cohomologous ω₂ ω₃ → Cohomologous ω₁ ω₃ := by
  intro h12 h23; have hsum : IsExact (n := n) (X := X) (k := k) ((ω₁.val - ω₂.val) + (ω₂.val - ω₃.val)) := isExact_add (n := n) (X := X) (k := k) (ω := (ω₁.val - ω₂.val)) (η := (ω₂.val - ω₃.val)) h12 h23
  dsimp [Cohomologous] at *; simpa [sub_eq_add_neg, add_assoc, add_comm] using hsum

instance DeRhamSetoid (n k : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Setoid (ClosedForm n X k) where
  r := Cohomologous
  iseqv := { refl := cohomologous_refl, symm := cohomologous_symm, trans := cohomologous_trans }

abbrev DeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Type u := Quotient (DeRhamSetoid n k X)

instance instAddCommGroupDeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : AddCommGroup (DeRhamCohomologyClass n X k) where
  add a b := Quotient.liftOn₂ a b (fun ω η => Quotient.mk _ (ω + η)) (by intro ω₁ ω₂ ω₁_prime ω₂_prime h1 h2; apply Quotient.sound; dsimp [Cohomologous] at h1 h2 ⊢; simpa [sub_eq_add_neg, add_assoc, add_comm] using isExact_add h1 h2)
  add_assoc a b c := by refine Quotient.inductionOn₃ a b c ?_; intro ω η θ; apply Quotient.sound; simpa [add_assoc] using cohomologous_refl _
  zero := Quotient.mk (DeRhamSetoid n k X) 0
  zero_add a := by refine Quotient.inductionOn a ?_; intro ω; apply Quotient.sound; simpa using cohomologous_refl _
  add_zero a := by refine Quotient.inductionOn a ?_; intro ω; apply Quotient.sound; simpa using cohomologous_refl _
  add_comm a b := by refine Quotient.inductionOn₂ a b ?_; intro ω η; apply Quotient.sound; dsimp [Cohomologous]; simpa [sub_eq_add_neg, add_assoc, add_comm] using isExact_zero k
  neg a := Quotient.liftOn a (fun ω => Quotient.mk _ (-ω)) (by intro ω ω_prime h; apply Quotient.sound; dsimp [Cohomologous] at h ⊢; simpa [sub_eq_add_neg, add_assoc, add_comm] using isExact_neg h)
  neg_add_cancel a := by refine Quotient.inductionOn a ?_; intro ω; apply Quotient.sound; simpa using cohomologous_refl _
  nsmul m a := Nat.rec (motive := fun _ => DeRhamCohomologyClass n X k) 0 (fun _ r => r + a) m
  nsmul_zero a := rfl
  nsmul_succ m a := rfl
  zsmul z a := Int.recOn z (fun m => Nat.rec (motive := fun _ => DeRhamCohomologyClass n X k) 0 (fun _ r => r + a) m) (fun m => -(Nat.rec (motive := fun _ => DeRhamCohomologyClass n X k) 0 (fun _ r => r + a) (m + 1)))
  zsmul_zero' a := rfl
  zsmul_succ' m a := rfl
  zsmul_neg' m a := rfl
  sub a b := a + -b
  sub_eq_add_neg a b := rfl

instance instModuleDeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Module ℂ (DeRhamCohomologyClass n X k) where
  smul c a := Quotient.liftOn a (fun ω => Quotient.mk _ (c • ω)) (by intro ω ω_prime h; apply Quotient.sound; dsimp [Cohomologous] at h ⊢; cases k with | zero => have h0 : ω.val - ω_prime.val = 0 := by simpa [IsExact] using h; simpa [sub_eq_add_neg, smul_add, smul_neg, h0] using isExact_zero 0 | succ k_pred => rcases h with ⟨α, hα⟩; refine ⟨c • α, ?_⟩; rw [smoothExtDeriv_smul, hα]; simp [sub_eq_add_neg, smul_add, smul_neg])
  one_smul a := by refine Quotient.inductionOn a ?_; intro ω; apply Quotient.sound; simpa using cohomologous_refl _
  mul_smul r s a := by refine Quotient.inductionOn a ?_; intro ω; apply Quotient.sound; simpa [mul_smul] using cohomologous_refl _
  smul_zero r := by apply Quotient.sound; simpa using cohomologous_refl _
  smul_add r a b := by refine Quotient.inductionOn₂ a b ?_; intro ω η; apply Quotient.sound; simpa [smul_add] using cohomologous_refl _
  add_smul r s a := by refine Quotient.inductionOn a ?_; intro ω; apply Quotient.sound; simpa [add_smul] using cohomologous_refl _
  zero_smul a := by refine Quotient.inductionOn a ?_; intro ω; apply Quotient.sound; simpa using cohomologous_refl _

instance instModuleRealDeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Module ℝ (DeRhamCohomologyClass n X k) where
  smul r a := ((r : ℂ) • a)
  one_smul a := by simp
  mul_smul r s a := by simp [mul_smul]
  smul_zero r := by simp
  smul_add r a b := by simp [smul_add]
  add_smul r s a := by simp [add_smul]
  zero_smul a := by simp

def DeRhamCohomologyClass.representative {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] (c : DeRhamCohomologyClass n X k) : SmoothForm n X k := (Quotient.out c).val
theorem DeRhamCohomologyClass.representative_closed {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] (c : DeRhamCohomologyClass n X k) : IsFormClosed (DeRhamCohomologyClass.representative c) := (Quotient.out c).property
def DeRhamCohomologyClass.ofForm {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] (ω : SmoothForm n X k) (h : IsFormClosed ω) : DeRhamCohomologyClass n X k := Quotient.mk (DeRhamSetoid n k X) ⟨ω, h⟩
notation "⟦" ω "," h "⟧" => DeRhamCohomologyClass.ofForm ω h
theorem ofForm_proof_irrel {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] (ω : SmoothForm n X k) (h₁ h₂ : IsFormClosed ω) : DeRhamCohomologyClass.ofForm ω h₁ = DeRhamCohomologyClass.ofForm ω h₂ := by unfold DeRhamCohomologyClass.ofForm; have : (⟨ω, h₁⟩ : ClosedForm n X k) = ⟨ω, h₂⟩ := by ext; rfl; simpa [this]

axiom ofForm_add {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : DeRhamCohomologyClass.ofForm (ω + η) (isFormClosed_add ω η hω hη) = DeRhamCohomologyClass.ofForm ω hω + DeRhamCohomologyClass.ofForm η hη
axiom ofForm_sub {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : DeRhamCohomologyClass.ofForm (ω - η) (isFormClosed_sub ω η hω hη) = DeRhamCohomologyClass.ofForm ω hω - DeRhamCohomologyClass.ofForm η hη
axiom ofForm_smul_rat {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] (q : ℚ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : DeRhamCohomologyClass.ofForm (q • ω) (isFormClosed_smul ((q : ℝ) : ℂ) ω hω) = q • DeRhamCohomologyClass.ofForm ω hω
axiom ofForm_smul_real {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] (r : ℝ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : DeRhamCohomologyClass.ofForm (r • ω) (isFormClosed_smul (r : ℂ) ω hω) = r • DeRhamCohomologyClass.ofForm ω hω
axiom DeRhamCohomologyClass.pairing {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] (η : DeRhamCohomologyClass n X k) (ψ : DeRhamCohomologyClass n X (2 * n - k)) : ℂ
opaque isRationalClass {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [KahlerManifold n X] {k : ℕ} (η : DeRhamCohomologyClass n X k) : Prop
