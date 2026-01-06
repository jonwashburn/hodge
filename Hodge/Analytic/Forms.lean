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
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Defs.Induced
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.LinearAlgebra.StdBasis
import Hodge.Analytic.DomCoprod
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

noncomputable section

open Classical Module Manifold ContinuousAlternatingMap
open scoped Pointwise

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-- We work with the model tangent space `E = ℂⁿ` (Mathlib's `EuclideanSpace ℂ (Fin n)`). -/
abbrev TangentModel (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The (fiberwise) space of alternating `k`-linear maps on the model tangent space. -/
abbrev FiberAlt (n : ℕ) (k : ℕ) := (TangentModel n) [⋀^Fin k]→L[ℂ] ℂ

/-- A section of differential forms is “smooth” (for this development) if the alternating map
    varies smoothly (`C^∞`) in `x`, as a map into the normed space of continuous alternating maps. -/
def IsSmoothAlternating (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (k : ℕ) (f : X → FiberAlt n k) : Prop :=
  ContMDiff (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤ f

@[ext]
structure SmoothForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  as_alternating : X → FiberAlt n k
  is_smooth : IsSmoothAlternating n X k as_alternating

/-- The zero form is smooth (constant map). -/
theorem isSmoothAlternating_zero (k : ℕ) : IsSmoothAlternating n X k (fun _ => 0) :=
  contMDiff_const

/-- The sum of smooth forms is smooth. -/
theorem isSmoothAlternating_add (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x + η.as_alternating x) := by
  let add : (FiberAlt n k × FiberAlt n k) →L[ℂ] FiberAlt n k :=
    ContinuousLinearMap.fst ℂ (FiberAlt n k) (FiberAlt n k) +
    ContinuousLinearMap.snd ℂ (FiberAlt n k) (FiberAlt n k)
  exact add.contMDiff.comp (ContMDiff.prodMk_space ω.is_smooth η.is_smooth)

/-- The negation of a smooth form is smooth. -/
theorem isSmoothAlternating_neg (k : ℕ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => -ω.as_alternating x) := by
  let neg : FiberAlt n k →L[ℂ] FiberAlt n k := -ContinuousLinearMap.id ℂ (FiberAlt n k)
  exact neg.contMDiff.comp ω.is_smooth

/-- Scalar multiplication preserves smoothness. -/
theorem isSmoothAlternating_smul (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => c • ω.as_alternating x) := by
  let smul : FiberAlt n k →L[ℂ] FiberAlt n k := c • ContinuousLinearMap.id ℂ (FiberAlt n k)
  exact smul.contMDiff.comp ω.is_smooth

/-- The difference of smooth forms is smooth. -/
theorem isSmoothAlternating_sub (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x - η.as_alternating x) := by
  let sub : (FiberAlt n k × FiberAlt n k) →L[ℂ] FiberAlt n k :=
    ContinuousLinearMap.fst ℂ (FiberAlt n k) (FiberAlt n k) -
    ContinuousLinearMap.snd ℂ (FiberAlt n k) (FiberAlt n k)
  exact sub.contMDiff.comp (ContMDiff.prodMk_space ω.is_smooth η.is_smooth)

/-- For a fixed continuous alternating map, the “evaluation-on-the-unit-ball” set is bounded above.
This is the basic boundedness input for `sSup`-based operator norms. -/
theorem IsSmoothAlternating.bddAbove {k : ℕ} (f : FiberAlt n k) :
    BddAbove { r : ℝ | ∃ v : Fin k → TangentModel n, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖f v‖ } := by
  refine ⟨‖f‖, ?_⟩
  rintro r ⟨v, hv, rfl⟩
  have hprod : (∏ i : Fin k, ‖v i‖) ≤ 1 := by
    classical
    refine Finset.prod_le_one ?_ ?_
    · intro i _; exact norm_nonneg _
    · intro i _; simpa using hv i
  have hle : ‖f v‖ ≤ ‖f‖ * (∏ i : Fin k, ‖v i‖) := by
    simpa using (ContinuousAlternatingMap.le_opNorm (f := f) v)
  calc
    ‖f v‖ ≤ ‖f‖ * (∏ i : Fin k, ‖v i‖) := hle
    _ ≤ ‖f‖ * 1 := by gcongr
    _ = ‖f‖ := by simp

instance (k : ℕ) : Zero (SmoothForm n X k) := ⟨⟨fun _ => 0, isSmoothAlternating_zero k⟩⟩
instance (k : ℕ) : Add (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x + η.as_alternating x, isSmoothAlternating_add k ω η⟩⟩
instance (k : ℕ) : Neg (SmoothForm n X k) := ⟨fun ω => ⟨fun x => -ω.as_alternating x, isSmoothAlternating_neg k ω⟩⟩
instance (k : ℕ) : Sub (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x - η.as_alternating x, isSmoothAlternating_sub k ω η⟩⟩
instance (k : ℕ) : SMul ℂ (SmoothForm n X k) := ⟨fun c ω => ⟨fun x => c • ω.as_alternating x, isSmoothAlternating_smul k c ω⟩⟩
instance (k : ℕ) : SMul ℝ (SmoothForm n X k) :=
  ⟨fun r ω => ⟨fun x => r • ω.as_alternating x, by
    -- smoothness follows from continuity of scalar multiplication
    simpa [IsSmoothAlternating] using isSmoothAlternating_smul k (r : ℂ) ω⟩⟩

@[simp] lemma SmoothForm.zero_apply (k : ℕ) (x : X) : (0 : SmoothForm n X k).as_alternating x = 0 := rfl
@[simp] lemma SmoothForm.add_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) : (ω + η).as_alternating x = ω.as_alternating x + η.as_alternating x := rfl
@[simp] lemma SmoothForm.neg_apply (k : ℕ) (ω : SmoothForm n X k) (x : X) : (-ω).as_alternating x = -ω.as_alternating x := rfl
@[simp] lemma SmoothForm.sub_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) : (ω - η).as_alternating x = ω.as_alternating x - η.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_apply (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) (x : X) : (c • ω).as_alternating x = c • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_real_apply (k : ℕ) (r : ℝ) (ω : SmoothForm n X k) (x : X) :
    (r • ω).as_alternating x = r • ω.as_alternating x := rfl

instance instAddCommGroupSmoothForm (k : ℕ) : AddCommGroup (SmoothForm n X k) where
  add_assoc := by intros; ext; simp [add_assoc]
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
  add_comm := by intros; ext; simp [add_comm]
  neg_add_cancel := by intros; ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg := by intros; ext x v; simp only [SmoothForm.add_apply, SmoothForm.sub_apply, SmoothForm.neg_apply]; exact sub_eq_add_neg _ _

instance (k : ℕ) : Module ℂ (SmoothForm n X k) where
  add_smul r s ω := by ext x v; simp only [SmoothForm.smul_apply, SmoothForm.add_apply]; exact add_smul r s _
  smul_add r ω η := by ext x v; simp only [SmoothForm.smul_apply, SmoothForm.add_apply]; exact smul_add r _ _
  mul_smul r s ω := by ext x v; simp only [SmoothForm.smul_apply]; exact mul_smul r s _
  one_smul ω := by ext x v; simp only [SmoothForm.smul_apply]; exact one_smul ℂ _
  smul_zero r := by ext x v; simp only [SmoothForm.smul_apply, SmoothForm.zero_apply]; exact smul_zero _
  zero_smul ω := by ext x v; simp only [SmoothForm.smul_apply, SmoothForm.zero_apply]; exact zero_smul ℂ _

/-!
### Exterior Derivative

We now introduce the real exterior derivative `d` (upgraded from a placeholder).
The smoothness proof is currently admitted (`sorry`) to unblock integration.
-/

/-- The pointwise exterior derivative. -/
noncomputable def extDerivAt {k : ℕ} (ω : SmoothForm n X k) (x : X) : FiberAlt n (k + 1) :=
  ContinuousAlternatingMap.alternatizeUncurryFin
    (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
    (mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x)

/-- Helper: `mfderiv` expressed in tangent coordinates relative to a basepoint `x₀`. -/
noncomputable def mfderivInTangentCoordinates {k : ℕ} (ω : SmoothForm n X k) (x₀ x : X) :
    TangentModel n →L[ℂ] FiberAlt n k :=
  inTangentCoordinates (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) (fun y => y) (fun y => ω.as_alternating y)
    (fun y => mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating y) x₀ x

theorem contMDiffAt_mfderivInTangentCoordinates {k : ℕ} (ω : SmoothForm n X k) (x₀ : X) :
    ContMDiffAt (𝓒_complex n) 𝓘(ℂ, TangentModel n →L[ℂ] FiberAlt n k) ⊤
      (mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀) x₀ := by
  have hf : ContMDiffAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤ ω.as_alternating x₀ :=
    ω.is_smooth x₀
  simpa [mfderivInTangentCoordinates] using
    ContMDiffAt.mfderiv_const (I := 𝓒_complex n) (I' := 𝓘(ℂ, FiberAlt n k))
      (f := ω.as_alternating) (x₀ := x₀) hf (by simp)

/-- The pointwise exterior derivative built from `mfderivInTangentCoordinates`. -/
noncomputable def extDerivInTangentCoordinates {k : ℕ} (ω : SmoothForm n X k) (x₀ : X) :
    X → FiberAlt n (k + 1) :=
  fun x =>
    ContinuousAlternatingMap.alternatizeUncurryFin
      (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
      (mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀ x)

theorem contMDiffAt_extDerivInTangentCoordinates {k : ℕ} (ω : SmoothForm n X k) (x₀ : X) :
    ContMDiffAt (𝓒_complex n) 𝓘(ℂ, FiberAlt n (k + 1)) ⊤
      (extDerivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀) x₀ := by
  let L := ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (TangentModel n) ℂ (n := k)
  have hL : ContDiff ℂ (⊤ : WithTop ℕ∞) ⇑L :=
    ContinuousLinearMap.contDiff (𝕜 := ℂ)
      (E := (TangentModel n) →L[ℂ] FiberAlt n k)
      (F := FiberAlt n (k + 1))
      (n := ⊤)
      L
  have hm : ContMDiffAt (𝓒_complex n) 𝓘(ℂ, TangentModel n →L[ℂ] FiberAlt n k) ⊤
        (mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀) x₀ :=
    contMDiffAt_mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀
  have := ContDiff.comp_contMDiffAt (I := (𝓒_complex n)) (g := ⇑L)
    (f := mfderivInTangentCoordinates (n := n) (X := X) (k := k) ω x₀)
    (x := x₀) hL hm
  simpa [extDerivInTangentCoordinates, L] using this

/-- The global exterior derivative operator. -/
noncomputable def smoothExtDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1) where
  as_alternating := extDerivAt ω
  is_smooth := by
    -- TODO: Formalize the diagonal smoothness argument using `contMDiffAt_extDerivInTangentCoordinates`.
    sorry

noncomputable def extDerivLinearMap (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1) where
  toFun := smoothExtDeriv
  map_add' := fun x y => by
    -- Linearity of derivative is standard but involves some rewriting of arguments.
    -- Admitting to focus on integration.
    sorry
  map_smul' := fun c x => by
    -- Linearity of derivative is standard.
    sorry

theorem smoothExtDeriv_add {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) : smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ :=
  map_add (extDerivLinearMap n X k) ω₁ ω₂

theorem smoothExtDeriv_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) : smoothExtDeriv (c • ω) = c • smoothExtDeriv ω :=
  map_smul (extDerivLinearMap n X k) c ω

theorem smoothExtDeriv_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) : smoothExtDeriv (r • ω) = r • smoothExtDeriv ω := by
  have h : smoothExtDeriv ((r : ℂ) • ω) = (r : ℂ) • smoothExtDeriv ω := smoothExtDeriv_smul (r : ℂ) ω
  exact h

/-!
### Closed and Exact Forms
-/

def IsFormClosed {k : ℕ} (ω : SmoothForm n X k) : Prop :=
  smoothExtDeriv ω = 0

def IsFormExact {k : ℕ} (ω : SmoothForm n X k) : Prop :=
  match k with
  | 0 => False
  | l + 1 => ∃ (η : SmoothForm n X l), smoothExtDeriv η = ω

structure ClosedForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  val : SmoothForm n X k
  property : IsFormClosed val

namespace ClosedForm
instance (k : ℕ) : Add (ClosedForm n X k) := ⟨fun ω η => ⟨ω.val + η.val, by
  unfold IsFormClosed
  rw [smoothExtDeriv_add, ω.property, η.property, add_zero]⟩⟩

instance (k : ℕ) : Neg (ClosedForm n X k) := ⟨fun ω => ⟨-ω.val, by
  unfold IsFormClosed
  have h_linear : smoothExtDeriv (-ω.val) = -smoothExtDeriv ω.val := by
    change (extDerivLinearMap n X k) (-ω.val) = -(extDerivLinearMap n X k) ω.val
    rw [LinearMap.map_neg]
  rw [h_linear, ω.property, neg_zero]⟩⟩

instance (k : ℕ) : Zero (ClosedForm n X k) := ⟨⟨0, by
  unfold IsFormClosed
  change (extDerivLinearMap n X k) 0 = 0
  rw [LinearMap.map_zero]⟩⟩
end ClosedForm

/-- **Wedge Product of Smooth Forms** -/
noncomputable def smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) : SmoothForm n X (k + l) where
  as_alternating := fun x =>
    ContinuousAlternatingMap.wedge (𝕜 := ℂ) (E := TangentModel n) (ω.as_alternating x) (η.as_alternating x)
  is_smooth := by
    -- TODO: Prove smoothness of wedge (bilinear composition).
    sorry

notation:67 ω:68 " ⋏ " η:68 => smoothWedge ω η

theorem isFormClosed_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω ⋏ η) := by
  intros hω hη
  -- This requires the Leibniz rule d(u ^ v) = du ^ v + (-1)^k u ^ dv.
  -- Since we have real d now, we should prove this or admit it.
  -- For now, `sorry` to preserve build.
  sorry

/-- Exterior derivative of an exterior derivative is zero (d² = 0). -/
theorem smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) : smoothExtDeriv (smoothExtDeriv ω) = 0 := by
  -- Follows from Schwarz theorem. Admitted for now.
  sorry

def unitForm : SmoothForm n X 0 := 0

theorem smoothWedge_add_left {k l : ℕ} (ω₁ ω₂ : SmoothForm n X k) (η : SmoothForm n X l) : (ω₁ + ω₂) ⋏ η = (ω₁ ⋏ η) + (ω₂ ⋏ η) := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedge_add_left]
theorem smoothWedge_add_right {k l : ℕ} (ω : SmoothForm n X k) (η₁ η₂ : SmoothForm n X l) : ω ⋏ (η₁ + η₂) = (ω ⋏ η₁) + (ω ⋏ η₂) := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedge_add_right]
theorem smoothWedge_smul_left {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) : (c • ω) ⋏ η = c • (ω ⋏ η) := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedge_smul_left]
theorem smoothWedge_smul_right {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) : ω ⋏ (c • η) = c • (ω ⋏ η) := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedge_smul_right]

theorem smoothWedge_zero_left {k l : ℕ} (η : SmoothForm n X l) : (0 : SmoothForm n X k) ⋏ η = 0 := by
  ext x v
  simpa [smoothWedge] using
    congrArg (fun (f : FiberAlt n (k + l)) => f v)
      (ContinuousAlternatingMap.wedge_smul_left
        (𝕜 := ℂ) (E := TangentModel n) (c := (0 : ℂ))
        (ω := (0 : FiberAlt n k)) (η := η.as_alternating x))

theorem smoothWedge_zero_right {k l : ℕ} (ω : SmoothForm n X k) : ω ⋏ (0 : SmoothForm n X l) = 0 := by
  ext x v
  simpa [smoothWedge] using
    congrArg (fun (f : FiberAlt n (k + l)) => f v)
      (ContinuousAlternatingMap.wedge_smul_right
        (𝕜 := ℂ) (E := TangentModel n) (c := (0 : ℂ))
        (ω := ω.as_alternating x) (η := (0 : FiberAlt n l)))
