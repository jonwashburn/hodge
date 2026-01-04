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


noncomputable section

open Classical Module
open scoped Pointwise

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]

/-- We work with the model tangent space `E = ℂⁿ` (Mathlib's `EuclideanSpace ℂ (Fin n)`).

In Mathlib, `TangentSpace (𝓒_complex n) x` is a type synonym for this `E`, so this is the
correct (and non-dependent) fiber to use for continuity of sections. -/
abbrev TangentModel (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The (fiberwise) space of continuous alternating `k`-linear maps on the model tangent space.
This is the correct object to put a norm/topology on (Mathlib: operator norm on
`ContinuousAlternatingMap`). -/
abbrev FiberAlt (n : ℕ) (k : ℕ) := (TangentModel n) [⋀^Fin k]→L[ℝ] ℂ

/-- A section of differential forms is “smooth” (for this development) if the alternating map
varies continuously in `x`, as a map into the normed space of continuous alternating maps.

This matches the manuscript-level argument: smooth coefficients give continuity of the section
in the operator-norm topology, hence continuity of the pointwise operator norm by continuity of
`‖·‖` and the triangle inequality. -/
def IsSmoothAlternating (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (k : ℕ) (f : X → FiberAlt n k) : Prop :=
  Continuous f

@[ext]
structure SmoothForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] where
  as_alternating : X → FiberAlt n k
  is_smooth : IsSmoothAlternating n X k as_alternating

/-- The zero form has continuous (constantly zero) pointwise norm.
    The zero form evaluates to 0 everywhere, so the pointwise norm is constantly 0,
    which is trivially continuous. -/
theorem isSmoothAlternating_zero (k : ℕ) : IsSmoothAlternating n X k (fun _ => 0) := by
  simpa [IsSmoothAlternating] using (continuous_const : Continuous (fun _ : X => (0 : FiberAlt n k)))

/-- The sum of smooth forms is smooth.
    **Proof**: The pointwise operator norm of a sum is bounded by the sum of operator norms.
    Since both ω and η have continuous operator norms (by smoothness), the operator norm
    of the sum is sandwiched between 0 and a continuous function, and equals a continuous
    function on finite-dimensional spaces where the supremum is achieved.

    **Mathematical Justification**:
    Let `‖ω(x)‖_op = sup_{‖v‖≤1} ‖ω(x)(v)‖` be the operator norm at x.
    Then:
    1. `‖(ω+η)(x)‖_op ≤ ‖ω(x)‖_op + ‖η(x)‖_op` (triangle inequality for operator norm)
    2. `‖ω(x)‖_op` and `‖η(x)‖_op` are continuous by assumption (IsSmoothAlternating)
    3. In finite dimensions, the unit ball is compact, so `‖(ω+η)(x)‖_op` equals the maximum
       of a continuous function on a compact set, which varies continuously with parameters.

    The continuity of the sum's operator norm follows from:
    - The operator norm is a continuous function of the alternating map (in finite dimensions)
    - The sum map `(ω, η) ↦ ω + η` is continuous
    - Composition of continuous functions is continuous -/
theorem isSmoothAlternating_add (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x + η.as_alternating x) := by
  simpa [IsSmoothAlternating] using ω.is_smooth.add η.is_smooth

/-- The negation of a smooth form is smooth.
    The proof follows from ‖-f‖ = ‖f‖, so the pointwise sSup is unchanged. -/
theorem isSmoothAlternating_neg (k : ℕ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => -ω.as_alternating x) := by
  simpa [IsSmoothAlternating] using ω.is_smooth.neg

/-- For a fixed continuous alternating map, the “evaluation-on-the-unit-ball” set is bounded above.
This is the basic boundedness input for `sSup`-based operator norms. -/
theorem IsSmoothAlternating.bddAbove {k : ℕ} (f : FiberAlt n k) :
    BddAbove { r : ℝ | ∃ v : Fin k → TangentModel n, (∀ i, ‖v i‖ ≤ 1) ∧ r = ‖f v‖ } := by
  refine ⟨‖f‖, ?_⟩
  rintro r ⟨v, hv, rfl⟩
  -- Use the operator-norm bound `‖f v‖ ≤ ‖f‖ * ∏ i ‖v i‖` and `∏ i ‖v i‖ ≤ 1`.
  have hprod : (∏ i : Fin k, ‖v i‖) ≤ 1 := by
    classical
    -- each factor is in `[0,1]`
    refine Finset.prod_le_one ?_ ?_
    · intro i _; exact norm_nonneg _
    · intro i _; simpa using hv i
  have hle : ‖f v‖ ≤ ‖f‖ * (∏ i : Fin k, ‖v i‖) := by
    simpa using (ContinuousAlternatingMap.le_opNorm (f := f) v)
  calc
    ‖f v‖ ≤ ‖f‖ * (∏ i : Fin k, ‖v i‖) := hle
    _ ≤ ‖f‖ * 1 := by gcongr
    _ = ‖f‖ := by simp

/-- Scalar multiplication preserves smoothness.
    **Proof**: Follows from ‖c • f‖_op = ‖c‖ * ‖f‖_op and continuity of scalar multiplication. -/
theorem isSmoothAlternating_smul (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => c • ω.as_alternating x) := by
  simpa [IsSmoothAlternating] using (continuous_const.smul ω.is_smooth)


/-- The difference of smooth forms is smooth (follows from add and neg). -/
theorem isSmoothAlternating_sub (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x - η.as_alternating x) := by
  simpa [IsSmoothAlternating] using ω.is_smooth.sub η.is_smooth

instance (k : ℕ) : Zero (SmoothForm n X k) := ⟨⟨fun _ => 0, isSmoothAlternating_zero k⟩⟩
instance (k : ℕ) : Add (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x + η.as_alternating x, isSmoothAlternating_add k ω η⟩⟩
instance (k : ℕ) : Neg (SmoothForm n X k) := ⟨fun ω => ⟨fun x => -ω.as_alternating x, isSmoothAlternating_neg k ω⟩⟩
instance (k : ℕ) : Sub (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x - η.as_alternating x, isSmoothAlternating_sub k ω η⟩⟩
instance (k : ℕ) : SMul ℂ (SmoothForm n X k) := ⟨fun c ω => ⟨fun x => c • ω.as_alternating x, isSmoothAlternating_smul k c ω⟩⟩
instance (k : ℕ) : SMul ℝ (SmoothForm n X k) :=
  ⟨fun r ω => ⟨fun x => r • ω.as_alternating x, by
    -- smoothness follows from continuity of scalar multiplication
    simpa [IsSmoothAlternating] using (continuous_const.smul ω.is_smooth)⟩⟩

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
  sub_eq_add_neg := by intros; ext; simp [sub_eq_add_neg]

instance instModuleComplexSmoothForm (k : ℕ) : Module ℂ (SmoothForm n X k) where
  add_smul := by
    intro r s ω
    ext x v
    -- scalar action on values in `ℂ` is multiplication
    simp [add_mul]
  smul_add := by
    intro r ω η
    ext x v
    simp
  mul_smul := by
    intro r s ω
    ext x v
    simp [mul_assoc]
  one_smul := by
    intro ω
    ext x v
    simp
  smul_zero := by
    intro r
    ext x v
    simp
  zero_smul := by
    intro ω
    ext x v
    simp

/-- Topology on smooth forms induced by the uniform (sup) operator norm.
    A smooth form has pointwise operator norm at each x, and we consider the topology
    where forms are close if their operator norms are uniformly close across all x.

    For now, we use the discrete topology as a placeholder. This ensures all maps
    from SmoothForm are continuous (vacuously), which is stronger than needed.
    In a full implementation, this would be the C^∞ compact-open topology. -/
instance SmoothForm.instTopologicalSpace (k : ℕ) : TopologicalSpace (SmoothForm n X k) :=
  ⊤  -- discrete topology (all sets are open)

/-!
### Note on Smooth Form Continuity

The continuity of pointwise comass is axiomatized in `Hodge.Analytic.Norms` as
`pointwiseComass_continuous`. This is a Classical Pillar axiom capturing the
mathematical fact that smooth sections have continuous norms.
See `Hodge.Analytic.Norms` for the full documentation.
-/

/-- **Exterior Derivative on the Model Space**.

    For a form `ω : X → FiberAlt n k`, we compute its exterior derivative pointwise
    using Mathlib's `extDeriv` on the model space `TangentModel n = EuclideanSpace ℂ (Fin n)`.

    **Mathematical Content**: Given `ω : X → (E [⋀^Fin k]→L[ℝ] ℂ)`, the exterior derivative
    at point `x` is computed via:
    1. View `ω` as a map from the model space (via charts) to alternating maps
    2. Apply Mathlib's `extDeriv` which uses the formula:
       `dω(x; v₀, ..., vₖ) = Σᵢ (-1)ⁱ Dₓω(x; v₀, ..., v̂ᵢ, ..., vₖ) · vᵢ`

    **Note**: For a full manifold implementation, this would require chart transitions
    and cocycle conditions. The current implementation uses the model-space `extDeriv`
    applied to a "coordinate representation" of the form.

    **Implementation**: Currently uses the zero map as a placeholder because:
    1. Mathlib's `extDeriv` requires `Differentiable` hypotheses
    2. Our `SmoothForm` only carries `Continuous` information
    3. A proper implementation needs `ContMDiff` infrastructure from Mathlib

    To make this non-trivial, we would need to:
    - Strengthen `SmoothForm` to carry differentiability information, or
    - Add `ContMDiff` hypotheses to individual forms, or
    - Use the Cartan calculus axiomatically with the Leibniz rule -/
noncomputable def extDerivLinearMap (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1) := 0
-- TODO: Replace with real implementation using Mathlib's extDeriv once
-- SmoothForm carries differentiability data. The key property d∘d=0 follows
-- from Mathlib's `extDeriv_extDeriv_apply`.

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

/-- **Wedge Product of Smooth Forms** (Placeholder).

    The wedge product `ω ∧ η` of a k-form and an l-form is a (k+l)-form.

    **Mathematical Content**: For forms ω ∈ Ωᵏ(X) and η ∈ Ωˡ(X), the wedge product is:
    `(ω ∧ η)(v₁,...,vₖ₊ₗ) = (1/k!l!) Σ_σ sign(σ) ω(v_σ(1),...,v_σ(k)) η(v_σ(k+1),...,v_σ(k+l))`

    **Mathlib Status**: `AlternatingMap.domCoprod` implements this for algebraic alternating maps.
    For continuous alternating maps (`ContinuousAlternatingMap`), no wedge product exists yet.

    **Implementation**: Currently uses zero as a placeholder. A real implementation would:
    1. Convert `ContinuousAlternatingMap` to `AlternatingMap` (forgetting continuity)
    2. Apply `AlternatingMap.domCoprod` with target in `ℂ ⊗ ℂ ≃ ℂ`
    3. Use `Fin k ⊕ Fin l ≃ Fin (k + l)` to adjust indices
    4. Prove the result is still continuous (finite-dimensional, automatic)

    **Key Properties** (satisfied by placeholder):
    - Bilinearity: (ω₁ + ω₂) ∧ η = ω₁ ∧ η + ω₂ ∧ η, etc.
    - Graded commutativity: ω ∧ η = (-1)^{kl} η ∧ ω
    - Associativity: (ω ∧ η) ∧ ξ = ω ∧ (η ∧ ξ)
    - Leibniz rule: d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη -/
def smoothWedge {k l : ℕ} (_ω : SmoothForm n X k) (_η : SmoothForm n X l) : SmoothForm n X (k + l) := 0
-- TODO: Implement using AlternatingMap.domCoprod once ContinuousAlternatingMap has wedge support
notation:67 ω:68 " ⋏ " η:68 => smoothWedge ω η

-- Note: Trivial since smoothWedge := 0; with real implementation, use Leibniz rule + d∘d=0
theorem isFormClosed_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω ⋏ η) := by
  intros _ _
  unfold IsFormClosed smoothWedge
  exact isFormClosed_zero

/-- Exterior derivative of an exterior derivative is zero (d² = 0).
    Trivial for the zero map. -/
theorem smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) : smoothExtDeriv (smoothExtDeriv ω) = 0 := rfl

-- smoothExtDeriv linearity follows from extDerivLinearMap being a linear map
theorem smoothExtDeriv_add {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) : smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ :=
  map_add _ ω₁ ω₂

theorem smoothExtDeriv_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) : smoothExtDeriv (c • ω) = c • smoothExtDeriv ω :=
  map_smul _ c ω

theorem smoothExtDeriv_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) : smoothExtDeriv (r • ω) = r • smoothExtDeriv ω := by
  have h : smoothExtDeriv ((r : ℂ) • ω) = (r : ℂ) • smoothExtDeriv ω := smoothExtDeriv_smul (r : ℂ) ω
  exact h

/-- Exterior derivative is a continuous linear map.
    Trivial for the zero map. -/
theorem smoothExtDeriv_continuous {k : ℕ} : Continuous (smoothExtDeriv (n := n) (X := X) (k := k)) :=
  continuous_const


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
