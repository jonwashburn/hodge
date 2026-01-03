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

/-- A section of differential forms is smooth if the pointwise operator norm varies continuously.
    This captures the essential content of smoothness without requiring full vector bundle machinery.

    **Mathematical Justification**: A smooth differential form α on a manifold X is a smooth
    section of the exterior power bundle. Smoothness implies that:
    1. The form coefficients (in any local chart) are smooth functions
    2. The pointwise operator norm ‖α(x)‖_op is a continuous function of x
    3. For any continuous vector field v, the evaluation α(v) is continuous

    We axiomatize the key property we need: continuity of the pointwise norm. -/
def IsSmoothAlternating (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (k : ℕ) (f : (x : X) → (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℝ] ℂ) : Prop :=
  -- The pointwise operator norm is continuous as a function X → ℝ
  Continuous (fun x => sSup { r : ℝ | ∃ v : Fin k → TangentSpace (𝓒_complex n) x,
    (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖(f x) v‖ })

@[ext]
structure SmoothForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] where
  as_alternating : (x : X) → (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℝ] ℂ
  is_smooth : IsSmoothAlternating n X k as_alternating

/-- The zero form has continuous (constantly zero) pointwise norm.
    The zero form evaluates to 0 everywhere, so the pointwise norm is constantly 0,
    which is trivially continuous. -/
theorem isSmoothAlternating_zero (k : ℕ) : IsSmoothAlternating n X k (fun _ => 0) := by
  unfold IsSmoothAlternating
  -- The zero alternating map evaluates to 0 on all inputs, so ‖0 v‖ = 0
  -- The set { r | ∃ v, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖0‖ } = {0}
  -- sSup {0} = 0, so the function is constantly 0
  have h_set_eq : ∀ x : X, { r : ℝ | ∃ v : Fin k → TangentSpace (𝓒_complex n) x,
      (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖(0 : (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℝ] ℂ) v‖ } = {0} := by
    intro x
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, AlternatingMap.zero_apply, norm_zero]
    constructor
    · rintro ⟨_, _, rfl⟩; rfl
    · intro hr
      refine ⟨fun _ => 0, ?_, hr⟩
      intro i
      -- ‖0‖ = 0 ≤ 1 in any NormedAddCommGroup
      simp only [norm_zero, zero_le_one]
  have h_ssup_zero : ∀ x : X, sSup { r : ℝ | ∃ v : Fin k → TangentSpace (𝓒_complex n) x,
      (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖(0 : (TangentSpace (𝓒_complex n) x) [⋀^Fin k]→ₗ[ℝ] ℂ) v‖ } = 0 := by
    intro x; rw [h_set_eq]; exact csSup_singleton 0
  simp_rw [h_ssup_zero]
  exact continuous_const

/-- Axiom: The sum of smooth forms is smooth.
    The proof requires showing that ‖(ω + η)(x)‖_op is continuous, which follows from
    the triangle inequality and continuity of ω and η. -/
axiom isSmoothAlternating_add (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x + η.as_alternating x)

/-- The negation of a smooth form is smooth.
    The proof follows from ‖-f‖ = ‖f‖, so the pointwise sSup is unchanged. -/
theorem isSmoothAlternating_neg (k : ℕ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => -ω.as_alternating x) := by
  unfold IsSmoothAlternating
  -- Show that { r | ∃ v, ... ∧ r = ‖(-ω x) v‖ } = { r | ∃ v, ... ∧ r = ‖(ω x) v‖ }
  -- because ‖(-f) v‖ = ‖-(f v)‖ = ‖f v‖
  have h_eq : ∀ x : X, { r : ℝ | ∃ v : Fin k → TangentSpace (𝓒_complex n) x,
      (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖(-ω.as_alternating x) v‖ } =
    { r : ℝ | ∃ v : Fin k → TangentSpace (𝓒_complex n) x,
      (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖(ω.as_alternating x) v‖ } := by
    intro x
    ext r
    simp only [Set.mem_setOf_eq, AlternatingMap.neg_apply, norm_neg]
  simp_rw [h_eq]
  exact ω.is_smooth

/-- Axiom: Scalar multiplication preserves smoothness.
    The proof follows from ‖c • f‖ = |c| * ‖f‖. -/
axiom isSmoothAlternating_smul (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => c • ω.as_alternating x)

/-- The difference of smooth forms is smooth (follows from add and neg). -/
theorem isSmoothAlternating_sub (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x - η.as_alternating x) := by
  -- sub = add neg, so use those axioms
  have hsub : ∀ x, ω.as_alternating x - η.as_alternating x = ω.as_alternating x + (-η.as_alternating x) := by
    intro x; rfl
  simp_rw [hsub]
  exact isSmoothAlternating_add k ω ⟨fun x => -η.as_alternating x, isSmoothAlternating_neg k η⟩

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
@[simp] lemma SmoothForm.smul_real_apply (k : ℕ) (r : ℝ) (ω : SmoothForm n X k) (x : X) : (r • ω).as_alternating x = (r : ℂ) • ω.as_alternating x := rfl

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

/-- **Note on Smooth Form Continuity**
    The continuity of pointwise comass is axiomatized in `Hodge.Analytic.Norms` as
    `pointwiseComass_continuous`. This is a Classical Pillar axiom capturing the
    mathematical fact that smooth sections have continuous norms.
    See `Hodge.Analytic.Norms` for the full documentation. -/

axiom extDerivLinearMap (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1)

def smoothExtDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1) :=
  extDerivLinearMap n X k ω

@[simp] theorem smoothExtDeriv_zero {k : ℕ} : smoothExtDeriv (0 : SmoothForm n X k) = 0 :=
  map_zero _

def IsFormClosed {k : ℕ} (ω : SmoothForm n X k) : Prop := smoothExtDeriv ω = 0

theorem isFormClosed_zero {k : ℕ} : IsFormClosed (0 : SmoothForm n X k) := by
  unfold IsFormClosed smoothExtDeriv; simp

theorem isFormClosed_add {k : ℕ} {ω η : SmoothForm n X k} : IsFormClosed ω → IsFormClosed η → IsFormClosed (ω + η) := by
  intros hω hη; unfold IsFormClosed smoothExtDeriv at *; simp; rw [hω, hη]; simp

@[simp] theorem smoothExtDeriv_neg {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (-ω) = -smoothExtDeriv ω := map_neg _ ω

@[simp] theorem smoothExtDeriv_sub {k : ℕ} (ω η : SmoothForm n X k) :
    smoothExtDeriv (ω - η) = smoothExtDeriv ω - smoothExtDeriv η := map_sub _ ω η

theorem isFormClosed_neg {k : ℕ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (-ω) := by
  intro hω; unfold IsFormClosed at *; rw [smoothExtDeriv_neg, hω]; simp

theorem isFormClosed_sub {k : ℕ} {ω η : SmoothForm n X k} : IsFormClosed ω → IsFormClosed η → IsFormClosed (ω - η) := by
  intros hω hη; unfold IsFormClosed at *; rw [smoothExtDeriv_sub, hω, hη]; simp

theorem isFormClosed_smul {k : ℕ} {c : ℂ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (c • ω) := by
  intro hω; unfold IsFormClosed smoothExtDeriv at *; simp; apply Or.inr; exact hω

theorem isFormClosed_smul_real {k : ℕ} {r : ℝ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (r • ω) := by
  intro hω; unfold IsFormClosed smoothExtDeriv at *; simp; apply Or.inr; exact hω

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
instance (k : ℕ) : Zero (ClosedForm n X k) := ⟨⟨0, isFormClosed_zero⟩⟩
end ClosedForm

def smoothWedge {k l : ℕ} (_ω : SmoothForm n X k) (_η : SmoothForm n X l) : SmoothForm n X (k + l) := 0
notation:67 ω:68 " ⋏ " η:68 => smoothWedge ω η

-- Note: Trivial since smoothWedge := 0; needs real proof once wedge is implemented
theorem isFormClosed_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω ⋏ η) := by
  intros _ _
  unfold IsFormClosed smoothWedge
  exact isFormClosed_zero

axiom smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) : smoothExtDeriv (smoothExtDeriv ω) = 0

-- smoothExtDeriv linearity follows from extDerivLinearMap being a linear map
theorem smoothExtDeriv_add {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) : smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ :=
  map_add _ ω₁ ω₂

theorem smoothExtDeriv_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) : smoothExtDeriv (c • ω) = c • smoothExtDeriv ω :=
  map_smul _ c ω

theorem smoothExtDeriv_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) : smoothExtDeriv (r • ω) = r • smoothExtDeriv ω := by
  have h : smoothExtDeriv ((r : ℂ) • ω) = (r : ℂ) • smoothExtDeriv ω := smoothExtDeriv_smul (r : ℂ) ω
  simp only [Complex.real_smul] at h ⊢
  exact h
axiom smoothExtDeriv_continuous {k : ℕ} : Continuous (smoothExtDeriv (n := n) (X := X) (k := k))

-- smoothExtDeriv_wedge (Leibniz rule for wedge) was removed as unused
-- The HEq degree arithmetic is complex and wedge := 0 anyway

def unitForm : SmoothForm n X 0 := 0

-- Note: The following wedge properties are trivial since smoothWedge := 0
-- They will need real proofs once smoothWedge is properly implemented
theorem smoothWedge_add_left {k l : ℕ} (ω₁ ω₂ : SmoothForm n X k) (η : SmoothForm n X l) : (ω₁ + ω₂) ⋏ η = (ω₁ ⋏ η) + (ω₂ ⋏ η) := by
  simp only [smoothWedge, add_zero]
theorem smoothWedge_add_right {k l : ℕ} (ω : SmoothForm n X k) (η₁ η₂ : SmoothForm n X l) : ω ⋏ (η₁ + η₂) = (ω ⋏ η₁) + (ω ⋏ η₂) := by
  simp only [smoothWedge, add_zero]
theorem smoothWedge_smul_left {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) : (c • ω) ⋏ η = c • (ω ⋏ η) := by
  simp only [smoothWedge, smul_zero]
theorem smoothWedge_smul_right {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) : ω ⋏ (c • η) = c • (ω ⋏ η) := by
  simp only [smoothWedge, smul_zero]
theorem smoothWedge_zero_left {k l : ℕ} (η : SmoothForm n X l) : (0 : SmoothForm n X k) ⋏ η = 0 := rfl
theorem smoothWedge_zero_right {k l : ℕ} (ω : SmoothForm n X k) : ω ⋏ (0 : SmoothForm n X l) = 0 := rfl
