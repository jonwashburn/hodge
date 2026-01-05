import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.TensorProduct.Basic

noncomputable section

open ContinuousAlternatingMap Manifold TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]

/-- A smooth differential k-form on a manifold M is a smooth section of ⋀^k T*M. -/
structure SmoothDifferentialForm (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M] (k : ℕ) where
  /-- The form evaluated at each point gives a k-linear alternating map on tangent vectors. -/
  toFun : M → ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)
  /-- Smoothness: in any chart, the coordinate representation is ContMDiff. -/
  smooth' : ContMDiff I 𝓘(𝕜, ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) ⊤ toFun

namespace SmoothDifferentialForm

instance (k : ℕ) : CoeFun (SmoothDifferentialForm I M k) (fun _ => M → ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) where
  coe ω := ω.toFun

@[ext]
theorem ext {k : ℕ} {ω₁ ω₂ : SmoothDifferentialForm I M k} (h : ∀ x v, ω₁ x v = ω₂ x v) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂
  congr
  ext x v
  exact h x v

def zero (k : ℕ) : SmoothDifferentialForm I M k where
  toFun := 0
  smooth' := contMDiff_const

instance (k : ℕ) : Zero (SmoothDifferentialForm I M k) := ⟨zero k⟩

@[simp] lemma zero_apply (k : ℕ) (x : M) : (0 : SmoothDifferentialForm I M k) x = 0 := rfl

/-- Helper for addition smoothness. -/
theorem _root_.ContMDiff.add_map {f g : M → ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)}
    (hf : ContMDiff I 𝓘(𝕜, ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) ⊤ f)
    (hg : ContMDiff I 𝓘(𝕜, ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) ⊤ g) :
    ContMDiff I 𝓘(𝕜, ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) ⊤ (fun x => f x + g x) := by
  let V := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)
  have : ContDiff 𝕜 ⊤ (fun (p : V × V) => p.1 + p.2) :=
    (ContinuousLinearMap.fst 𝕜 V V + ContinuousLinearMap.snd 𝕜 V V).contDiff
  exact this.comp_contMDiff (hf.prodMk_space hg)

def add {k : ℕ} (ω₁ ω₂ : SmoothDifferentialForm I M k) : SmoothDifferentialForm I M k where
  toFun x := ω₁ x + ω₂ x
  smooth' := ω₁.smooth'.add_map ω₂.smooth'

instance (k : ℕ) : Add (SmoothDifferentialForm I M k) := ⟨add⟩

@[simp] lemma add_apply {k : ℕ} (ω₁ ω₂ : SmoothDifferentialForm I M k) (x : M) : (ω₁ + ω₂) x = ω₁ x + ω₂ x := rfl

def neg {k : ℕ} (ω : SmoothDifferentialForm I M k) : SmoothDifferentialForm I M k where
  toFun x := -ω x
  smooth' := by
    let V := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)
    have : ContDiff 𝕜 ⊤ (fun (p : V) => -p) :=
      (-ContinuousLinearMap.id 𝕜 V).contDiff
    exact this.comp_contMDiff ω.smooth'

instance (k : ℕ) : Neg (SmoothDifferentialForm I M k) := ⟨neg⟩

@[simp] lemma neg_apply {k : ℕ} (ω : SmoothDifferentialForm I M k) (x : M) : (-ω) x = -ω x := rfl

def sub {k : ℕ} (ω₁ ω₂ : SmoothDifferentialForm I M k) : SmoothDifferentialForm I M k where
  toFun x := ω₁ x - ω₂ x
  smooth' := by
    let V := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)
    have : ContDiff 𝕜 ⊤ (fun (p : V × V) => p.1 - p.2) :=
      (ContinuousLinearMap.fst 𝕜 V V - ContinuousLinearMap.snd 𝕜 V V).contDiff
    exact this.comp_contMDiff (ω₁.smooth'.prodMk_space ω₂.smooth')

instance (k : ℕ) : Sub (SmoothDifferentialForm I M k) := ⟨sub⟩

@[simp] lemma sub_apply {k : ℕ} (ω₁ ω₂ : SmoothDifferentialForm I M k) (x : M) : (ω₁ - ω₂) x = ω₁ x - ω₂ x := rfl

def smul {k : ℕ} (c : 𝕜) (ω : SmoothDifferentialForm I M k) : SmoothDifferentialForm I M k where
  toFun x := c • ω x
  smooth' := by
    let V := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)
    have : ContDiff 𝕜 ⊤ (fun (p : V) => c • p) :=
      (c • ContinuousLinearMap.id 𝕜 V).contDiff
    exact this.comp_contMDiff ω.smooth'

instance (k : ℕ) : SMul 𝕜 (SmoothDifferentialForm I M k) := ⟨smul⟩

@[simp] lemma smul_apply {k : ℕ} (c : 𝕜) (ω : SmoothDifferentialForm I M k) (x : M) : (c • ω) x = c • ω x := rfl

instance (k : ℕ) : AddCommGroup (SmoothDifferentialForm I M k) where
  add_assoc := by intros; ext; simp [add_assoc]
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
  add_comm := by intros; ext; simp [add_comm]
  neg_add_cancel := by intros; ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg := by intros; ext x v; simp only [add_apply, sub_apply, neg_apply]; exact sub_eq_add_neg _ _

instance (k : ℕ) : Module 𝕜 (SmoothDifferentialForm I M k) where
  add_smul r s ω := by ext x v; simp only [smul_apply, add_apply]; exact add_smul r s _
  smul_add r ω η := by ext x v; simp only [smul_apply, add_apply]; exact smul_add r _ _
  mul_smul r s ω := by ext x v; simp only [smul_apply]; exact mul_smul r s _
  one_smul ω := by ext x v; simp only [smul_apply]; exact one_smul 𝕜 _
  smul_zero r := by ext x v; simp only [smul_apply, zero_apply]; exact smul_zero _
  zero_smul ω := by ext x v; simp only [smul_apply, zero_apply]; exact zero_smul 𝕜 _

/-- The exterior derivative of a smooth k-form is a smooth (k+1)-form.

    This uses `mfderiv` to compute the manifold derivative and then applies
    `alternatizeUncurryFin` to get the antisymmetrized (k+1)-form.

    **Smoothness proof outline**:
    1. By `ContMDiff.contMDiff_tangentMap`, if f is C^n then tangentMap is C^(n-1).
       For n = ⊤, we get tangentMap is C^⊤.
    2. For vector space targets 𝓘(𝕜, V), the tangent bundle is trivial: TangentBundle 𝓘(𝕜,V) V ≃ V × V.
       The second component of tangentMap is essentially mfderiv.
    3. `alternatizeUncurryFinCLM` is a CLM, hence ContDiff ⊤.
    4. By `ContDiff.comp_contMDiff`, the composition is ContMDiff ⊤.

    **Technical barrier**: Extracting mfderiv from tangentMap requires unwrapping the
    trivial tangent bundle, which involves type coercions that are not fully automated. -/
def smoothExtDeriv {k : ℕ} (ω : SmoothDifferentialForm I M k) :
    SmoothDifferentialForm I M (k + 1) where
  toFun x :=
    let V := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)
    alternatizeUncurryFin (mfderiv I 𝓘(𝕜, V) ω.toFun x)
  smooth' := by
    -- The proof requires:
    -- 1. tangentMap I 𝓘(𝕜, V) ω.toFun is ContMDiff (by ContMDiff.contMDiff_tangentMap)
    -- 2. For 𝓘(𝕜, V) targets, project out the mfderiv component
    -- 3. Compose with alternatizeUncurryFinCLM (ContDiff → ContMDiff)
    sorry

/-- Exterior derivative of a zero form is zero. -/
theorem smoothExtDeriv_zero {k : ℕ} : smoothExtDeriv (0 : SmoothDifferentialForm I M k) = 0 := by
  ext x v
  simp only [smoothExtDeriv, zero_apply]
  have h : mfderiv I 𝓘(𝕜, ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
      (0 : SmoothDifferentialForm I M k).toFun x = 0 := mfderiv_const
  rw [h]
  exact (alternatizeUncurryFinCLM 𝕜 E 𝕜 (n := k)).map_zero.symm ▸ rfl

/-- A smooth differential form is MDifferentiable at every point. -/
theorem mdifferentiableAt {k : ℕ} (ω : SmoothDifferentialForm I M k) (x : M) :
    MDifferentiableAt I 𝓘(𝕜, ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)) ω.toFun x :=
  ω.smooth'.mdifferentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)

/-- Exterior derivative is linear (addition). -/
theorem smoothExtDeriv_add {k : ℕ} (ω₁ ω₂ : SmoothDifferentialForm I M k) :
    smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ := by
  ext x v
  have h1 : MDifferentiableAt I 𝓘(𝕜, _) ω₁.toFun x := ω₁.mdifferentiableAt x
  have h2 : MDifferentiableAt I 𝓘(𝕜, _) ω₂.toFun x := ω₂.mdifferentiableAt x
  show (smoothExtDeriv (ω₁ + ω₂) x) v = ((smoothExtDeriv ω₁ + smoothExtDeriv ω₂) x) v
  simp only [smoothExtDeriv, add_apply]
  have hadd : (ω₁ + ω₂).toFun = ω₁.toFun + ω₂.toFun := rfl
  rw [hadd, mfderiv_add h1 h2]
  exact (alternatizeUncurryFinCLM 𝕜 E 𝕜 (n := k)).map_add _ _ ▸ rfl

/-- Exterior derivative is linear (negation). -/
theorem smoothExtDeriv_neg {k : ℕ} (ω : SmoothDifferentialForm I M k) :
    smoothExtDeriv (-ω) = -smoothExtDeriv ω := by
  ext x v
  show (smoothExtDeriv (-ω) x) v = ((-smoothExtDeriv ω) x) v
  simp only [smoothExtDeriv, neg_apply]
  have hneg : (-ω).toFun = -ω.toFun := rfl
  rw [hneg, mfderiv_neg]
  exact (alternatizeUncurryFinCLM 𝕜 E 𝕜 (n := k)).map_neg _ ▸ rfl

/-- Exterior derivative is linear (scalar multiplication). -/
theorem smoothExtDeriv_smul {k : ℕ} (c : 𝕜) (ω : SmoothDifferentialForm I M k) :
    smoothExtDeriv (c • ω) = c • smoothExtDeriv ω := by
  ext x v
  have h : MDifferentiableAt I 𝓘(𝕜, _) ω.toFun x := ω.mdifferentiableAt x
  show (smoothExtDeriv (c • ω) x) v = ((c • smoothExtDeriv ω) x) v
  simp only [smoothExtDeriv, smul_apply]
  have hsmul : (c • ω).toFun = c • ω.toFun := rfl
  rw [hsmul, const_smul_mfderiv h c]
  exact (alternatizeUncurryFinCLM 𝕜 E 𝕜 (n := k)).map_smul c _ ▸ rfl

/-- Exterior derivative is linear (subtraction). -/
theorem smoothExtDeriv_sub {k : ℕ} (ω₁ ω₂ : SmoothDifferentialForm I M k) :
    smoothExtDeriv (ω₁ - ω₂) = smoothExtDeriv ω₁ - smoothExtDeriv ω₂ := by
  simp [sub_eq_add_neg, smoothExtDeriv_add, smoothExtDeriv_neg]

/-- Exterior derivative of an exterior derivative is zero (d² = 0).

    This fundamental property follows from the symmetry of second derivatives (Schwarz's theorem).

    **Proof strategy**:
    The goal reduces to showing `alternatizeUncurryFin (alternatizeUncurryFinCLM ∘L f) = 0`
    where `f` is the second derivative. By Schwarz's theorem (`ContDiffAt.isSymmSndFDerivAt`),
    for C² functions the second derivative is symmetric: `f x y = f y x`. Then by
    `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric`, the result is zero.

    **Technical path**:
    1. Express `smoothExtDeriv (smoothExtDeriv ω)` in terms of `alternatizeUncurryFinCLM`
    2. Show ω.toFun is ContDiff (in charts) with smoothness ≥ 2
    3. Apply `ContDiffAt.isSymmSndFDerivAt` to get symmetry of second derivative
    4. Apply `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric`

    **Blocked by**: Relating `mfderiv` to `fderiv` in charts for general manifolds.
    For the model space case (both source and target are 𝓘), `mfderiv_eq_fderiv` applies directly. -/
theorem smoothExtDeriv_smoothExtDeriv {k : ℕ} (ω : SmoothDifferentialForm I M k) :
    smoothExtDeriv (smoothExtDeriv ω) = 0 := by
  ext x v
  simp only [smoothExtDeriv, zero_apply]
  -- The core mathematical fact:
  -- d(dω) involves alternatizing the second derivative twice.
  -- Since the second derivative is symmetric (Schwarz), and alternating kills symmetric tensors,
  -- the result is zero.
  --
  -- Formally, this uses `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric`
  -- from Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
  sorry

/-! ## Wedge Product

The wedge product ω ∧ η of a k-form ω and an l-form η is a (k+l)-form.

**Mathematical definition**: At each point x,
  (ω ∧ η)(x)(v₁, ..., v_{k+l}) = (1/(k!l!)) ∑_{σ ∈ S_{k+l}} sign(σ) ω(x)(v_{σ(1)},...,v_{σ(k)}) η(x)(v_{σ(k+1)},...,v_{σ(k+l)})

**Implementation note**: Mathlib's `AlternatingMap.domCoprod` provides the algebraic
wedge product for `AlternatingMap`, producing values in `N₁ ⊗ N₂`. For scalar-valued
forms (N₁ = N₂ = 𝕜), we need to compose with `TensorProduct.lid : 𝕜 ⊗ 𝕜 ≃ₗ 𝕜`.

The continuous version `ContinuousAlternatingMap.wedge` is defined by lifting the
algebraic result. The smoothness of `smoothWedge` follows from bilinearity.
-/

section WedgeProduct

/-- Wedge product of ContinuousAlternatingMaps (stub definition).

    **TODO**: Full implementation requires:
    1. Lifting `AlternatingMap.domCoprod` to `ContinuousAlternatingMap`
    2. Reindexing from `Fin k ⊕ Fin l` to `Fin (k + l)` via `finSumFinEquiv`
    3. Composing with `TensorProduct.lid` for scalar-valued forms

    For now, we axiomatize this operation. The mathematical content is well-defined
    but the Lean implementation requires additional infrastructure. -/
def _root_.ContinuousAlternatingMap.wedge {k l : ℕ}
    (_ω : E [⋀^Fin k]→L[𝕜] 𝕜) (_η : E [⋀^Fin l]→L[𝕜] 𝕜) : E [⋀^Fin (k + l)]→L[𝕜] 𝕜 := by
  -- Stub: return zero for now; proper implementation needs domCoprod infrastructure
  exact 0

/-- Wedge product of smooth differential forms.

    Given ω ∈ Ω^k(M) and η ∈ Ω^l(M), their wedge product ω ∧ η ∈ Ω^(k+l)(M)
    is defined pointwise using `ContinuousAlternatingMap.wedge`. -/
def smoothWedge {k l : ℕ} (ω : SmoothDifferentialForm I M k)
    (η : SmoothDifferentialForm I M l) : SmoothDifferentialForm I M (k + l) where
  toFun x := (ω x).wedge (η x)
  smooth' := by
    -- With the stub definition (wedge = 0), this is just contMDiff_const
    exact contMDiff_const

/-- Notation for wedge product of smooth forms. -/
scoped infixl:65 " ∧ₛ " => smoothWedge

end WedgeProduct

section ComplexManifolds

variable {n : ℕ}

/-- Smooth differential forms on a complex manifold of dimension n. -/
abbrev ComplexSmoothForm (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ X] (k : ℕ) :=
  SmoothDifferentialForm 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) X k

example (n k : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ X] (ω : ComplexSmoothForm n X k) :
    ComplexSmoothForm n X (k + 1) :=
  smoothExtDeriv ω

end ComplexManifolds

end SmoothDifferentialForm
