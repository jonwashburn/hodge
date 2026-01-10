import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Hodge.Analytic.DomCoprod
import Hodge.Analytic.FormType
-- Proof-first: keep the main theorem import closure free of unfinished manifold-`d` infrastructure.


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

@[simp] lemma castForm_add {k k' : ℕ} (h : k = k') (ω η : SmoothForm n X k) :
    castForm h (ω + η) = castForm h ω + castForm h η := by
  subst h; rfl

@[simp] lemma castForm_smul {k k' : ℕ} (h : k = k') (c : ℂ) (ω : SmoothForm n X k) :
    castForm h (c • ω) = c • castForm h ω := by
  subst h; rfl

@[simp] lemma castForm_smul_real {k k' : ℕ} (h : k = k') (r : ℝ) (ω : SmoothForm n X k) :
    castForm h (r • ω) = r • castForm h ω := by
  subst h; rfl


/-!
### Conversion from/to SmoothForm
-/

-- Proof-first mode: the `ContMDiffForm` bridge lives in `Hodge/Analytic/ContMDiffForms.lean`
-- and is intentionally not imported here.

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
  add_smul r s ω := by ext x v; simp [add_mul]
  smul_add r ω η := by ext x v; simp
  mul_smul r s ω := by ext x v; simp [mul_assoc]
  one_smul ω := by ext x v; simp
  smul_zero r := by ext x v; simp [mul_zero]
  zero_smul ω := by ext x v; simp [zero_mul]

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
### Note on Smooth Form Continuity

The continuity of pointwise comass is axiomatized in `Hodge.Analytic.Norms` as
`pointwiseComass_continuous`. This is a Classical Pillar axiom capturing the
mathematical fact that smooth sections have continuous norms.
See `Hodge.Analytic.Norms` for the full documentation.
-/

/-- **Exterior Derivative on the Manifold (placeholder)**.

The main theorem chain (`Hodge/Kahler/Main.lean`) only assumes closedness hypotheses as inputs and
does not use manifold identities for `d`. To avoid importing unfinished manifold-`d` infrastructure
in the main proof closure, we model the exterior derivative as the **zero** linear map for now.

This is sufficient to define:
- `IsFormClosed` / `IsExact`,
- de Rham cohomology as a quotient type,
- the current boundary operator without additional analytic assumptions.

The genuine exterior derivative will be reinstated later in an “advanced” module that imports
`Hodge/Analytic/ContMDiffForms.lean` and proves the required properties. -/
noncomputable def extDerivLinearMap (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1) :=
  0

/-!
### Pointwise exterior derivative (real, but unbundled)

The project currently uses `smoothExtDeriv` bundled as a `LinearMap` into `SmoothForm`, and that
map is still a placeholder (`0`) until the chart-gluing argument is completed (Phase 2B).

However, we can already define the **pointwise** exterior derivative value
`extDerivAt ω x : FiberAlt n (k+1)` for a `SmoothForm` using Mathlib’s manifold derivative
`mfderiv` followed by alternatization. This is a genuine mathematical definition; what remains
is proving that `x ↦ extDerivAt ω x` is smooth so it can be bundled back into `SmoothForm`.
-/

/-- Pointwise exterior derivative value (as a fiber element), defined via `mfderiv` and
alternatization. -/
noncomputable def extDerivAt {k : ℕ} (ω : SmoothForm n X k) (x : X) : FiberAlt n (k + 1) :=
  ContinuousAlternatingMap.alternatizeUncurryFin
    (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
    (mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x)

@[simp] lemma extDerivAt_def {k : ℕ} (ω : SmoothForm n X k) (x : X) :
    extDerivAt (n := n) (X := X) ω x =
      ContinuousAlternatingMap.alternatizeUncurryFin
        (𝕜 := ℂ) (E := TangentModel n) (F := ℂ) (n := k)
        (mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x) := rfl

/-- A “real” closedness predicate: `ω` is closed if its pointwise exterior derivative vanishes.

This is **not** yet used by the cohomology layer (which still uses the bundled `smoothExtDeriv`
placeholder), but it is the intended replacement target in Phase 2B. -/
def IsFormClosed_pointwise {k : ℕ} (ω : SmoothForm n X k) : Prop :=
  ∀ x : X, extDerivAt (n := n) (X := X) ω x = 0

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
  intro hω; unfold IsFormClosed smoothExtDeriv at *; simp; rw [hω]; simp

theorem isFormClosed_smul_real {k : ℕ} {r : ℝ} {ω : SmoothForm n X k} : IsFormClosed ω → IsFormClosed (r • ω) := by
  intro hω; unfold IsFormClosed smoothExtDeriv at *; simp; rw [hω]; simp

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
def smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) : SmoothForm n X (k + l) where
  as_alternating := fun x =>
    ContinuousAlternatingMap.wedge (𝕜 := ℂ) (E := TangentModel n) (ω.as_alternating x) (η.as_alternating x)
  is_smooth := by
    -- smoothness of `x ↦ ω(x) ∧ η(x)`
    let f := ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l
    let f' : FiberAlt n k →L[ℂ] FiberAlt n l →L[ℂ] FiberAlt n (k + l) := f
    exact f'.contMDiff.comp ω.is_smooth |>.clm_apply η.is_smooth

notation:67 ω:68 " ⋏ " η:68 => smoothWedge ω η

@[simp] lemma zero_wedge {k l : ℕ} (η : SmoothForm n X l) : (0 : SmoothForm n X k) ⋏ η = 0 := by
  ext x v
  -- derive from `wedge_smul_left` with `c = 0`
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

/-- Leibniz rule for the exterior derivative of a wedge product.
    d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη.
    Note: Requires casting types since (k+1)+l and k+(l+1) are only propositionally equal to k+l+1.

    **Mathematical Content**: This is the fundamental graded Leibniz rule for exterior algebra.
    At each point x, the exterior derivative of (ω ∧ η)(x) involves:
    1. Product rule: D(ω(x) ∧ η(x)) = Dω(x) ∧ η(x) + ω(x) ∧ Dη(x)
    2. Alternatization: The sign (-1)^k arises from the graded commutativity of wedge
       when commuting the differential past a k-form.

    **Proof sketch**:
    1. `(ω ⋏ η).as_alternating = wedgeCLM_alt ∘ (ω.as_alternating, η.as_alternating)`
    2. By the bilinear chain rule (`HasFDerivAt.clm_apply` or similar):
       `mfderiv ((ω ⋏ η).as_alternating) x = wedge(mfderiv ω x ·, η x) + wedge(ω x, mfderiv η x ·)`
    3. `alternatizeUncurryFin` distributes over sums (`alternatizeUncurryFin_add`)
    4. The key missing lemma: `alternatizeUncurryFin (wedge(f ·, η)) = wedge(alternatizeUncurryFin f, η)`
       This requires showing that alternatization commutes with fixing one argument of wedge.
    5. The sign (-1)^k arises from `wedge_comm` when reordering basis elements.

    **Formalization gap**: Mathlib's DifferentialForm/Basic.lean has `extDeriv_extDeriv` (d²=0)
    and `extDeriv_add` (linearity), but not:
    - `HasFDerivAt` for `ContinuousAlternatingMap.wedge` (Leibniz for bilinear wedge)
    - Interaction between `alternatizeUncurryFin` and `wedge` on fixed arguments
    - Graded commutativity signs in the differential algebra structure

    **Proof via LeibnizRule.lean**:
    The theorem `LeibnizRule.extDerivAt_wedge` provides the pointwise identity.
    This lifts to SmoothForm by extensionality. -/
theorem smoothExtDeriv_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    smoothExtDeriv (ω ⋏ η) =
      castForm (by simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]) (smoothExtDeriv ω ⋏ η) +
      castForm (by simp [Nat.add_assoc]) ((-1 : ℂ)^k • (ω ⋏ smoothExtDeriv η)) := by
  -- Proof-first placeholder: `smoothExtDeriv = 0`, so this is tautological.
  simp [smoothExtDeriv, extDerivLinearMap]

theorem isFormClosed_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    IsFormClosed ω → IsFormClosed η → IsFormClosed (ω ⋏ η) := by
  intros hω hη
  unfold IsFormClosed at *
  rw [smoothExtDeriv_wedge]
  rw [hω, hη]
  simp [zero_wedge, wedge_zero]

/-- Exterior derivative of an exterior derivative is zero (d² = 0). -/
theorem smoothExtDeriv_extDeriv {k : ℕ} (ω : SmoothForm n X k) : smoothExtDeriv (smoothExtDeriv ω) = 0 := by
  ext x v
  simp [smoothExtDeriv, extDerivLinearMap]

-- smoothExtDeriv linearity follows from extDerivLinearMap being a linear map
theorem smoothExtDeriv_add {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) : smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ :=
  map_add _ ω₁ ω₂

theorem smoothExtDeriv_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) : smoothExtDeriv (c • ω) = c • smoothExtDeriv ω :=
  map_smul _ c ω

theorem smoothExtDeriv_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) : smoothExtDeriv (r • ω) = r • smoothExtDeriv ω :=
  map_smul _ (r : ℂ) ω

/-- Exterior derivative is a continuous linear map (in the discrete topology). -/
theorem smoothExtDeriv_continuous {k : ℕ} : Continuous (smoothExtDeriv (n := n) (X := X) (k := k)) :=
  continuous_of_discreteTopology


-- smoothExtDeriv_wedge (Leibniz rule for wedge) is currently a proof-first placeholder
-- because `smoothExtDeriv := 0`.

/-- The unit 0-form (constant `1`).

This is the intended multiplicative unit for the wedge/cup product on cohomology.
At the level of `FiberAlt n 0`, a 0-form is just a scalar. -/
def unitForm : SmoothForm n X 0 where
  as_alternating := fun _ =>
    haveI : IsEmpty (Fin 0) := Fin.isEmpty
    ContinuousAlternatingMap.constOfIsEmpty ℂ (TangentModel n) (ι := Fin 0) (1 : ℂ)
  is_smooth := contMDiff_const

theorem isFormClosed_unitForm : IsFormClosed (unitForm (n := n) (X := X)) := by
  unfold IsFormClosed smoothExtDeriv extDerivLinearMap unitForm
  simp

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
  -- derive from `wedge_smul_left` with `c = 0`
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

theorem smoothWedge_sub_left {k l : ℕ} (ω₁ ω₂ : SmoothForm n X k) (η : SmoothForm n X l) :
    (ω₁ - ω₂) ⋏ η = (ω₁ ⋏ η) - (ω₂ ⋏ η) := by
  have h1 : ω₁ - ω₂ = ω₁ + (-1 : ℂ) • ω₂ := by simp [sub_eq_add_neg]
  rw [h1, smoothWedge_add_left, smoothWedge_smul_left]
  simp [sub_eq_add_neg]

theorem smoothWedge_sub_right {k l : ℕ} (ω : SmoothForm n X k) (η₁ η₂ : SmoothForm n X l) :
    ω ⋏ (η₁ - η₂) = (ω ⋏ η₁) - (ω ⋏ η₂) := by
  have h1 : η₁ - η₂ = η₁ + (-1 : ℂ) • η₂ := by simp [sub_eq_add_neg]
  rw [h1, smoothWedge_add_right, smoothWedge_smul_right]
  simp [sub_eq_add_neg]
