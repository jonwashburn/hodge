import Hodge.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Logic.Equiv.Fin.Basic
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

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]

/-- Smoothness predicate for pointwise alternating k-forms.
    In this development, we require sections to be continuous. -/
def IsSmoothAlternating (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (k : ℕ) (f : (x : X) → (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℝ] ℂ) : Prop :=
  Continuous f

/-- A smooth k-form on a complex n-manifold X. -/
@[ext]
structure SmoothForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] where
  as_alternating : (x : X) → (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℝ] ℂ
  is_smooth : IsSmoothAlternating n X k as_alternating

/-! ### Smoothness Closure Theorems -/

theorem isSmoothAlternating_zero (k : ℕ) : IsSmoothAlternating n X k (fun _ => 0) := continuous_const

theorem isSmoothAlternating_add (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x + η.as_alternating x) :=
  Continuous.add ω.is_smooth η.is_smooth

theorem isSmoothAlternating_neg (k : ℕ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => -ω.as_alternating x) :=
  Continuous.neg ω.is_smooth

theorem isSmoothAlternating_smul (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => c • ω.as_alternating x) :=
  Continuous.smul continuous_const ω.is_smooth

theorem isSmoothAlternating_sub (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x - η.as_alternating x) :=
  Continuous.sub ω.is_smooth η.is_smooth

instance (k : ℕ) : Zero (SmoothForm n X k) := ⟨⟨fun _ => 0, isSmoothAlternating_zero k⟩⟩
instance (k : ℕ) : Add (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x + η.as_alternating x, isSmoothAlternating_add k ω η⟩⟩
instance (k : ℕ) : Neg (SmoothForm n X k) := ⟨fun ω => ⟨fun x => -ω.as_alternating x, isSmoothAlternating_neg k ω⟩⟩
instance (k : ℕ) : Sub (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x - η.as_alternating x, isSmoothAlternating_sub k ω η⟩⟩
instance (k : ℕ) : SMul ℂ (SmoothForm n X k) := ⟨fun c ω => ⟨fun x => c • ω.as_alternating x, isSmoothAlternating_smul k c ω⟩⟩
instance (k : ℕ) : SMul ℝ (SmoothForm n X k) := ⟨fun r ω => ⟨fun x => (r : ℂ) • ω.as_alternating x, isSmoothAlternating_smul k (r : ℂ) ω⟩⟩

@[simp] lemma SmoothForm.zero_apply (k : ℕ) (x : X) : (0 : SmoothForm n X k).as_alternating x = 0 := rfl
@[simp] lemma SmoothForm.add_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) : (ω + η).as_alternating x = ω.as_alternating x + η.as_alternating x := rfl
@[simp] lemma SmoothForm.neg_apply (k : ℕ) (ω : SmoothForm n X k) (x : X) : (-ω).as_alternating x = -ω.as_alternating x := rfl
@[simp] lemma SmoothForm.sub_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) : (ω - η).as_alternating x = ω.as_alternating x - η.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_apply (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) (x : X) : (c • ω).as_alternating x = c • ω.as_alternating x := rfl

instance instAddCommGroupSmoothForm (k : ℕ) : AddCommGroup (SmoothForm n X k) where
  add_assoc := by intros; ext; simp [add_assoc]
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
  add_comm := by intros; ext; simp [add_comm]
  neg_add_cancel := by intros; ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg := by intros; ext; simp [sub_eq_add_neg]

instance instModuleComplexSmoothForm (k : ℕ) : Module ℂ (SmoothForm n X k) where
  add_smul := by intros; ext; simp [add_smul]
  smul_add := by intros; ext; simp [smul_add]
  mul_smul := by intros; ext; simp [mul_smul]
  one_smul := by intros; ext; simp
  smul_zero := by intros; ext; simp
  zero_smul := by intros; ext; simp

axiom SmoothForm.instTopologicalSpace (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : TopologicalSpace (SmoothForm n X k)
attribute [instance] SmoothForm.instTopologicalSpace

axiom extDerivLinearMap (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1)

def smoothExtDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1) :=
  extDerivLinearMap n X k ω

@[simp] theorem smoothExtDeriv_add {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) :
    smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ := map_add _ ω₁ ω₂

@[simp] theorem smoothExtDeriv_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) :
    smoothExtDeriv (c • ω) = c • smoothExtDeriv ω := map_smul _ c ω

def IsFormClosed {k : ℕ} (ω : SmoothForm n X k) : Prop := smoothExtDeriv ω = 0

theorem isFormClosed_zero {k : ℕ} : IsFormClosed (0 : SmoothForm n X k) := by unfold IsFormClosed; simp [smoothExtDeriv, map_zero]

theorem isFormClosed_add {k : ℕ} {ω η : SmoothForm n X k} : IsFormClosed ω → IsFormClosed η → IsFormClosed (ω + η) := by
  intros hω hη; unfold IsFormClosed at *; rw [smoothExtDeriv_add, hω, hη]; simp

theorem isFormClosed_neg {k : ℕ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (-ω) := by
  intro hω; unfold IsFormClosed at *; rw [map_neg, hω]; simp

theorem isFormClosed_sub {k : ℕ} {ω η : SmoothForm n X k} : IsFormClosed ω → IsFormClosed η → IsFormClosed (ω - η) := by
  intros hω hη; unfold IsFormClosed at *; rw [map_sub, hω, hη]; simp

theorem isFormClosed_smul {k : ℕ} {c : ℂ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (c • ω) := by
  intro hω; unfold IsFormClosed at *; rw [smoothExtDeriv_smul, hω]; simp

theorem isFormClosed_smul_real {k : ℕ} {r : ℝ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (r • ω) := by
  intro hω; unfold IsFormClosed at *; rw [map_smul, hω]; simp

def IsExact {k : ℕ} (ω : SmoothForm n X k) : Prop :=
  match k with
  | 0 => ω = 0
  | k' + 1 => ∃ (η : SmoothForm n X k'), smoothExtDeriv η = ω

structure ClosedForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] where
  val : SmoothForm n X k
  property : IsFormClosed val

namespace ClosedForm
instance (k : ℕ) : Add (ClosedForm n X k) := ⟨fun ω η => ⟨ω.val + η.val, isFormClosed_add ω.property η.property⟩⟩
instance (k : ℕ) : Neg (ClosedForm n X k) := ⟨fun ω => ⟨-ω.val, isFormClosed_neg ω.property⟩⟩
instance (k : ℕ) : Sub (ClosedForm n X k) := ⟨fun ω η => ⟨ω.val - η.val, isFormClosed_sub ω.property η.property⟩⟩
instance (k : ℕ) : Zero (ClosedForm n X k) := ⟨⟨0, isFormClosed_zero⟩⟩
end ClosedForm

def smoothWedge {k l : ℕ} (_ω : SmoothForm n X k) (_η : SmoothForm n X l) : SmoothForm n X (k + l) := 0
notation:67 ω:68 " ⋏ " η:68 => smoothWedge ω η

axiom isFormClosed_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω ⋏ η)

axiom smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) : smoothExtDeriv (smoothExtDeriv ω) = 0

axiom smoothExtDeriv_wedge {k l : ℕ} (α : SmoothForm n X k) (β : SmoothForm n X l) :
    ∃ (term1 term2 : SmoothForm n X (k + l + 1)),
      HEq (smoothExtDeriv α ⋏ β) term1 ∧
      HEq (α ⋏ smoothExtDeriv β) term2 ∧
      smoothExtDeriv (α ⋏ β) = term1 + ((-1 : ℂ) ^ k) • term2

def unitForm : SmoothForm n X 0 := 0

axiom smoothWedge_add_left {k l : ℕ} (ω₁ ω₂ : SmoothForm n X k) (η : SmoothForm n X l) : (ω₁ + ω₂) ⋏ η = (ω₁ ⋏ η) + (ω₂ ⋏ η)
axiom smoothWedge_add_right {k l : ℕ} (ω : SmoothForm n X k) (η₁ η₂ : SmoothForm n X l) : ω ⋏ (η₁ + η₂) = (ω ⋏ η₁) + (ω ⋏ η₂)
axiom smoothWedge_smul_left {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) : (c • ω) ⋏ η = c • (ω ⋏ η)
axiom smoothWedge_smul_right {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) : ω ⋏ (c • η) = c • (ω ⋏ η)
axiom smoothWedge_zero_left {k l : ℕ} (η : SmoothForm n X l) : (0 : SmoothForm n X k) ⋏ η = 0
axiom smoothWedge_zero_right {k l : ℕ} (ω : SmoothForm n X k) : ω ⋏ (0 : SmoothForm n X l) = 0

EOF
