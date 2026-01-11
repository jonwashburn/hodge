import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Hodge.Analytic.DomCoprod
import Hodge.Analytic.FormType
import Hodge.Basic


noncomputable section

open Classical Module Manifold
open scoped Pointwise Manifold

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-- The zero form has smooth (constantly zero) coefficients. -/
theorem isSmoothAlternating_zero (k : ℕ) : IsSmoothAlternating n X k (fun _ => 0) :=
  contMDiff_const

instance (k : ℕ) : Zero (SmoothForm n X k) := ⟨⟨fun _ => 0, isSmoothAlternating_zero k⟩⟩

/-- The sum of smooth forms is smooth. -/
theorem isSmoothAlternating_add (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x + η.as_alternating x) := by
  let addCLM : (FiberAlt n k × FiberAlt n k) →L[ℂ] FiberAlt n k :=
    ContinuousLinearMap.fst ℂ (FiberAlt n k) (FiberAlt n k) +
    ContinuousLinearMap.snd ℂ (FiberAlt n k) (FiberAlt n k)
  exact addCLM.contMDiff.comp (ω.is_smooth.prodMk_space η.is_smooth)

/-- The negation of a smooth form is smooth. -/
theorem isSmoothAlternating_neg (k : ℕ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => -ω.as_alternating x) := by
  let negCLM : FiberAlt n k →L[ℂ] FiberAlt n k := -ContinuousLinearMap.id ℂ (FiberAlt n k)
  exact negCLM.contMDiff.comp ω.is_smooth

/-- For a fixed continuous alternating map, the "evaluation-on-the-unit-ball" set is bounded above.
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

/-- Scalar multiplication preserves smoothness. -/
theorem isSmoothAlternating_smul (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => c • ω.as_alternating x) := by
  let smulCLM : FiberAlt n k →L[ℂ] FiberAlt n k := c • ContinuousLinearMap.id ℂ (FiberAlt n k)
  exact smulCLM.contMDiff.comp ω.is_smooth


/-- The difference of smooth forms is smooth (follows from add and neg). -/
theorem isSmoothAlternating_sub (k : ℕ) (ω η : SmoothForm n X k) :
    IsSmoothAlternating n X k (fun x => ω.as_alternating x - η.as_alternating x) := by
  let subCLM : (FiberAlt n k × FiberAlt n k) →L[ℂ] FiberAlt n k :=
    ContinuousLinearMap.fst ℂ (FiberAlt n k) (FiberAlt n k) -
    ContinuousLinearMap.snd ℂ (FiberAlt n k) (FiberAlt n k)
  exact subCLM.contMDiff.comp (ω.is_smooth.prodMk_space η.is_smooth)

instance (k : ℕ) : Add (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x + η.as_alternating x, isSmoothAlternating_add k ω η⟩⟩
instance (k : ℕ) : Neg (SmoothForm n X k) := ⟨fun ω => ⟨fun x => -ω.as_alternating x, isSmoothAlternating_neg k ω⟩⟩
instance (k : ℕ) : Sub (SmoothForm n X k) := ⟨fun ω η => ⟨fun x => ω.as_alternating x - η.as_alternating x, isSmoothAlternating_sub k ω η⟩⟩
instance (k : ℕ) : SMul ℂ (SmoothForm n X k) := ⟨fun c ω => ⟨fun x => c • ω.as_alternating x, isSmoothAlternating_smul k c ω⟩⟩
instance (k : ℕ) : SMul ℝ (SmoothForm n X k) :=
  ⟨fun r ω => ⟨fun x => r • ω.as_alternating x, isSmoothAlternating_smul k (r : ℂ) ω⟩⟩

@[simp] lemma SmoothForm.zero_apply (k : ℕ) (x : X) : (0 : SmoothForm n X k).as_alternating x = 0 := rfl
@[simp] lemma SmoothForm.add_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) : (ω + η).as_alternating x = ω.as_alternating x + η.as_alternating x := rfl
@[simp] lemma SmoothForm.neg_apply (k : ℕ) (ω : SmoothForm n X k) (x : X) : (-ω).as_alternating x = -ω.as_alternating x := rfl
@[simp] lemma SmoothForm.sub_apply (k : ℕ) (ω η : SmoothForm n X k) (x : X) : (ω - η).as_alternating x = ω.as_alternating x - η.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_apply (k : ℕ) (c : ℂ) (ω : SmoothForm n X k) (x : X) : (c • ω).as_alternating x = c • ω.as_alternating x := rfl
@[simp] lemma SmoothForm.smul_real_apply (k : ℕ) (r : ℝ) (ω : SmoothForm n X k) (x : X) :
    (r • ω).as_alternating x = r • ω.as_alternating x := rfl

/-- Cast a `SmoothForm` between equal degrees. -/
def castForm {k k' : ℕ} (h : k = k') (ω : SmoothForm n X k) : SmoothForm n X k' :=
  h ▸ ω

@[simp] lemma castForm_refl (k : ℕ) (ω : SmoothForm n X k) : castForm rfl ω = ω := rfl

@[simp] lemma castForm_zero {k k' : ℕ} (h : k = k') : castForm h (0 : SmoothForm n X k) = 0 := by
  subst h; rfl

@[simp] lemma SmoothForm.castForm_as_alternating {k k' : ℕ} (h : k = k') (ω : SmoothForm n X k) (x : X) :
    (castForm h ω).as_alternating x = h ▸ ω.as_alternating x := by
  subst h; rfl

instance (k : ℕ) : AddCommGroup (SmoothForm n X k) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  sub := (· - ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := fun ω η θ => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.add_apply, add_assoc]
  zero_add := fun ω => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.add_apply, SmoothForm.zero_apply, zero_add]
  add_zero := fun ω => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.add_apply, SmoothForm.zero_apply, add_zero]
  neg_add_cancel := fun ω => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.add_apply, SmoothForm.neg_apply, SmoothForm.zero_apply, neg_add_cancel]
  add_comm := fun ω η => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.add_apply, add_comm]
  sub_eq_add_neg := fun ω η => by
    apply SmoothForm.ext; funext x; simp only [SmoothForm.sub_apply, SmoothForm.add_apply, SmoothForm.neg_apply, sub_eq_add_neg]

instance (k : ℕ) : Module ℂ (SmoothForm n X k) where
  one_smul ω := by
    ext x v
    simp
  mul_smul c c' ω := by
    ext x v
    simp [mul_assoc]
  smul_zero c := by
    ext x v
    simp
  smul_add c ω η := by
    ext x v
    simp [mul_add]
  add_smul c c' ω := by
    ext x v
    simp [add_mul]
  zero_smul ω := by
    ext x v
    simp

/-- Topology on smooth forms induced by the uniform (sup) operator norm.
    A smooth form has pointwise operator norm at each x, and we consider the topology
    where forms are close if their operator norms are uniformly close across all x.

    For now, we use the discrete topology as a placeholder. This ensures all maps
    from SmoothForm are continuous (vacuously), which is stronger than needed.
    In a full implementation, this would be the C^∞ compact-open topology. -/
instance SmoothForm.instTopologicalSpace (k : ℕ) : TopologicalSpace (SmoothForm n X k) :=
  ⊥  -- discrete topology

instance (k : ℕ) : DiscreteTopology (SmoothForm n X k) := ⟨rfl⟩

/-!
### Exterior Derivative on Smooth Forms

The exterior derivative `d : Ωᵏ(X) → Ωᵏ⁺¹(X)` is defined using axioms that capture
its fundamental properties. The construction uses the manifold derivative `mfderiv`
followed by alternatization:

  `(dω)ₓ(v₀, v₁, ..., vₖ) = Alt(D(ω)(x))(v₀, v₁, ..., vₖ)`

where `D(ω)(x) : TₓX → Altᵏ(TₓX, ℂ)` is the derivative of the coefficient map.

**Key properties** (axiomatized below):
- Linearity: `d(αω + βη) = α·dω + β·dη`
- `d² = 0`: `d(dω) = 0` (by symmetry of second derivatives)
- Leibniz: `d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη`
-/

/-- **The exterior derivative as a ℂ-linear map (Axiomatized)**.

    This is axiomatized as a "Classical Pillar" of differential geometry.
    The exterior derivative `d : Ωᵏ(X) → Ωᵏ⁺¹(X)` satisfies:
    - Linearity: `d(αω + βη) = α·dω + β·dη`
    - `d² = 0`: `d(dω) = 0` (Poincaré lemma)
    - Leibniz: `d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη`

    The axiomatization avoids the need to work through the details of
    mfderiv and alternatization while preserving the essential structure. -/
axiom extDerivLinearMap (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1)

/-- The exterior derivative of a smooth form. -/
noncomputable def smoothExtDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1) :=
  extDerivLinearMap n X k ω

@[simp] theorem smoothExtDeriv_zero {k : ℕ} : smoothExtDeriv (0 : SmoothForm n X k) = 0 := by
  simp only [smoothExtDeriv, map_zero]

def IsFormClosed {k : ℕ} (ω : SmoothForm n X k) : Prop := smoothExtDeriv ω = 0

theorem isFormClosed_zero {k : ℕ} : IsFormClosed (0 : SmoothForm n X k) := by
  unfold IsFormClosed
  exact smoothExtDeriv_zero

theorem isFormClosed_add {k : ℕ} {ω η : SmoothForm n X k} :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω + η) := by
  intro hω hη
  unfold IsFormClosed at hω hη ⊢
  have hω' : (extDerivLinearMap n X k) ω = 0 := by
    simpa [smoothExtDeriv] using hω
  have hη' : (extDerivLinearMap n X k) η = 0 := by
    simpa [smoothExtDeriv] using hη
  change (extDerivLinearMap n X k) (ω + η) = 0
  rw [map_add (extDerivLinearMap n X k) ω η, hω', hη']
  simp

@[simp] theorem smoothExtDeriv_neg {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (-ω) = -smoothExtDeriv ω := map_neg (extDerivLinearMap n X k) ω

@[simp] theorem smoothExtDeriv_sub {k : ℕ} (ω η : SmoothForm n X k) :
    smoothExtDeriv (ω - η) = smoothExtDeriv ω - smoothExtDeriv η :=
  map_sub (extDerivLinearMap n X k) ω η

theorem isFormClosed_neg {k : ℕ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (-ω) := by
  intro hω; unfold IsFormClosed at *; rw [smoothExtDeriv_neg, hω]; simp

theorem isFormClosed_sub {k : ℕ} {ω η : SmoothForm n X k} :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω - η) := by
  intros hω hη; unfold IsFormClosed at *; rw [smoothExtDeriv_sub, hω, hη]; simp

theorem isFormClosed_smul {k : ℕ} {c : ℂ} {ω : SmoothForm n X k} :
    IsFormClosed ω → IsFormClosed (c • ω) := by
  intro hω
  unfold IsFormClosed at hω ⊢
  have hω' : (extDerivLinearMap n X k) ω = 0 := by
    simpa [smoothExtDeriv] using hω
  change (extDerivLinearMap n X k) (c • ω) = 0
  rw [map_smul (extDerivLinearMap n X k) c ω, hω']
  simp

theorem isFormClosed_smul_real {k : ℕ} {r : ℝ} {ω : SmoothForm n X k} :
    IsFormClosed ω → IsFormClosed (r • ω) := by
  intro hω
  have h : (r • ω) = ((r : ℂ) • ω) := rfl
  rw [h]
  exact isFormClosed_smul hω

def IsExact {k : ℕ} (ω : SmoothForm n X k) : Prop :=
  match k with
  | 0 => ω = 0
  | k' + 1 => ∃ (η : SmoothForm n X k'), smoothExtDeriv η = ω

/-- The zero form is exact at any degree. -/
theorem isExact_zero {k : ℕ} : IsExact (0 : SmoothForm n X k) := by
  unfold IsExact
  cases k with
  | zero => rfl
  | succ k' => exact ⟨0, smoothExtDeriv_zero⟩

structure ClosedForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  val : SmoothForm n X k
  property : IsFormClosed val

namespace ClosedForm
instance (k : ℕ) : Add (ClosedForm n X k) := ⟨fun ω η => ⟨ω.val + η.val, isFormClosed_add ω.property η.property⟩⟩
instance (k : ℕ) : Neg (ClosedForm n X k) := ⟨fun ω => ⟨-ω.val, isFormClosed_neg ω.property⟩⟩
instance (k : ℕ) : Zero (ClosedForm n X k) := ⟨⟨0, isFormClosed_zero⟩⟩
end ClosedForm

/-- **Wedge Product of Smooth Forms**.

    The wedge product `ω ∧ η` of a k-form and an l-form is a (k+l)-form.

    **Mathematical Content**: For forms ω ∈ Ωᵏ(X) and η ∈ Ωˡ(X), the wedge product is:
    `(ω ∧ η)(v₁,...,vₖ₊ₗ) = (1/k!l!) Σ_σ sign(σ) ω(v_σ(1),...,v_σ(k)) η(v_σ(k+1),...,v_σ(k+l))`

    **Smoothness**: Follows from the fact that `wedge` is a continuous bilinear map
    on finite-dimensional spaces, hence `ContMDiff`. -/
axiom isSmoothAlternating_wedge (k l : ℕ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsSmoothAlternating n X (k + l)
      (fun x => ContinuousAlternatingMap.wedge (𝕜 := ℂ) (E := TangentModel n)
                  (ω.as_alternating x) (η.as_alternating x))

noncomputable def smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) : SmoothForm n X (k + l) where
  as_alternating := fun x =>
    ContinuousAlternatingMap.wedge (𝕜 := ℂ) (E := TangentModel n)
      (ω.as_alternating x) (η.as_alternating x)
  is_smooth := isSmoothAlternating_wedge k l ω η

notation:67 ω:68 " ⋏ " η:68 => smoothWedge ω η

@[simp] lemma SmoothForm.wedge_apply {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) (x : X) :
    (ω ⋏ η).as_alternating x = ContinuousAlternatingMap.wedge (ω.as_alternating x) (η.as_alternating x) := rfl

@[simp] lemma zero_wedge {k l : ℕ} (η : SmoothForm n X l) : (0 : SmoothForm n X k) ⋏ η = 0 := by
  ext x v
  simpa [smoothWedge] using
    congrArg (fun (f : FiberAlt n (k + l)) => f v)
      (ContinuousAlternatingMap.wedge_smul_left
        (𝕜 := ℂ) (E := TangentModel n) (c := (0 : ℂ))
        (ω := (0 : FiberAlt n k)) (η := η.as_alternating x))

@[simp] lemma wedge_zero {k l : ℕ} (ω : SmoothForm n X k) : ω ⋏ (0 : SmoothForm n X l) = 0 := by
  ext x v
  simpa [smoothWedge] using
    congrArg (fun (f : FiberAlt n (k + l)) => f v)
      (ContinuousAlternatingMap.wedge_smul_right
        (𝕜 := ℂ) (E := TangentModel n) (c := (0 : ℂ))
        (ω := ω.as_alternating x) (η := (0 : FiberAlt n l)))

/-- **Axiom: d² = 0 (Exterior derivative squares to zero)**.

    This is the fundamental property of the de Rham complex, following from the
    symmetry of second derivatives (Schwarz's theorem / equality of mixed partials).

    For a smooth form ω, `d(dω) = 0` because the second derivative tensor is symmetric
    but alternatization kills symmetric components. -/
axiom smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) :
    smoothExtDeriv (smoothExtDeriv ω) = 0

/-- **Axiom: Leibniz rule for exterior derivative**.

    d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη

    The sign (-1)^k comes from the graded structure of differential forms:
    moving the derivative past a k-form requires k transpositions. -/
axiom smoothExtDeriv_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    smoothExtDeriv (ω ⋏ η) =
      castForm (by omega : (k + 1) + l = (k + l) + 1) (smoothExtDeriv ω ⋏ η) +
      castForm (by omega : k + (l + 1) = (k + l) + 1) ((-1 : ℂ)^k • (ω ⋏ smoothExtDeriv η))

theorem isFormClosed_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω ⋏ η) := by
  intros hω hη
  unfold IsFormClosed at *
  rw [smoothExtDeriv_wedge]
  rw [hω, hη]
  simp [zero_wedge, wedge_zero]

-- smoothExtDeriv linearity follows from extDerivLinearMap being a linear map
theorem smoothExtDeriv_add {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) :
    smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ :=
  map_add (extDerivLinearMap n X k) ω₁ ω₂

theorem smoothExtDeriv_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) :
    smoothExtDeriv (c • ω) = c • smoothExtDeriv ω :=
  map_smul (extDerivLinearMap n X k) c ω

theorem smoothExtDeriv_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) :
    smoothExtDeriv (r • ω) = r • smoothExtDeriv ω :=
  map_smul (extDerivLinearMap n X k) (r : ℂ) ω

/-- Exterior derivative is a continuous linear map (in the discrete topology). -/
theorem smoothExtDeriv_continuous {k : ℕ} : Continuous (smoothExtDeriv (n := n) (X := X) (k := k)) :=
  continuous_of_discreteTopology

/-- The unit 0-form (constant `1`).

This is the intended multiplicative unit for the wedge/cup product on cohomology.
At the level of `FiberAlt n 0`, a 0-form is just a scalar. -/
def unitForm : SmoothForm n X 0 where
  as_alternating := fun _ =>
    haveI : IsEmpty (Fin 0) := Fin.isEmpty
    ContinuousAlternatingMap.constOfIsEmpty ℂ (TangentModel n) (ι := Fin 0) (1 : ℂ)
  is_smooth := contMDiff_const

axiom isFormClosed_unitForm : IsFormClosed (unitForm (n := n) (X := X))

theorem smoothWedge_add_left {k l : ℕ} (ω₁ ω₂ : SmoothForm n X k) (η : SmoothForm n X l) :
    (ω₁ + ω₂) ⋏ η = (ω₁ ⋏ η) + (ω₂ ⋏ η) := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedge_add_left]

theorem smoothWedge_add_right {k l : ℕ} (ω : SmoothForm n X k) (η₁ η₂ : SmoothForm n X l) :
    ω ⋏ (η₁ + η₂) = (ω ⋏ η₁) + (ω ⋏ η₂) := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedge_add_right]

theorem smoothWedge_smul_left {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    (c • ω) ⋏ η = c • (ω ⋏ η) := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedge_smul_left]

theorem smoothWedge_smul_right {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    ω ⋏ (c • η) = c • (ω ⋏ η) := by
  ext x v
  simp [smoothWedge, ContinuousAlternatingMap.wedge_smul_right]

theorem smoothWedge_zero_left {k l : ℕ} (η : SmoothForm n X l) :
    (0 : SmoothForm n X k) ⋏ η = 0 := zero_wedge η

theorem smoothWedge_zero_right {k l : ℕ} (ω : SmoothForm n X k) :
    ω ⋏ (0 : SmoothForm n X l) = 0 := wedge_zero ω

/-- Wedge of unit form with any k-form gives back the k-form (up to degree cast).

For a k-form ω, the 0-form `unitForm` acts as a multiplicative unit:
- `unitForm x = constOfIsEmpty 1` (the scalar 1 as a 0-form)
- `(unitForm ⋏ ω) x = wedge (constOfIsEmpty 1) (ω x) = 1 • ω x = ω x`

The result lives in `Fin (0 + k)` which equals `Fin k` propositionally. -/
axiom smoothWedge_unitForm_left {k : ℕ} (ω : SmoothForm n X k) :
    unitForm ⋏ ω = castForm (Nat.zero_add k).symm ω

/-- Wedge of any k-form with unit form gives back the k-form (up to degree cast). -/
axiom smoothWedge_unitForm_right {k : ℕ} (ω : SmoothForm n X k) :
    ω ⋏ unitForm = castForm (Nat.add_zero k).symm ω

/-- Wedge product on smooth forms is associative (up to index equivalence). -/
axiom smoothWedge_assoc {k l m : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) (θ : SmoothForm n X m) :
    (ω ⋏ η) ⋏ θ = castForm (Nat.add_assoc k l m).symm (ω ⋏ (η ⋏ θ))

end
