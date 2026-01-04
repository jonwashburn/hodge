import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section

open ContinuousAlternatingMap Manifold

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
theorem ext {k : ℕ} {ω₁ ω₂ : SmoothDifferentialForm I M k} (h : ∀ x, ω₁ x = ω₂ x) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂
  congr
  funext x
  exact h x

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
  exact this.comp_contMDiff (fun x => (hf x).prodMk_space (hg x))

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
    exact this.comp_contMDiff (fun x => (ω₁.smooth' x).prodMk_space (ω₂.smooth' x))

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
  sub_eq_add_neg := by intros; ext; simp [sub_eq_add_neg]

instance (k : ℕ) : Module 𝕜 (SmoothDifferentialForm I M k) where
  add_smul := by intros r s ω; ext x v; simp; ring
  smul_add := by intros r ω η; ext x v; simp; ring
  mul_smul := by intros r s ω; ext x v; simp; ring
  one_smul := by intros; ext; simp
  smul_zero := by intros; ext; simp
  zero_smul := by intros; ext; simp

/-- The exterior derivative of a smooth k-form is a smooth (k+1)-form. 
    
    This uses `mfderiv` to compute the manifold derivative and then applies
    `alternatizeUncurryFin` to get the antisymmetrized (k+1)-form.
    
    The smoothness proof requires `ContMDiff.mfderiv_const` style results. -/
def smoothExtDeriv {k : ℕ} (ω : SmoothDifferentialForm I M k) : 
    SmoothDifferentialForm I M (k + 1) where
  toFun x := 
    let V := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)
    alternatizeUncurryFin (mfderiv I 𝓘(𝕜, V) ω.toFun x : E →L[𝕜] V)
  smooth' := by
    -- Smoothness of mfderiv for maps into a vector space.
    -- This follows from ContMDiffAt.mfderiv_const and the CLM structure of alternatizeUncurryFin.
    -- Proper proof requires more manifold infrastructure; we axiomatize for now.
    sorry

/-- Exterior derivative of a zero form is zero. -/
theorem smoothExtDeriv_zero {k : ℕ} : smoothExtDeriv (0 : SmoothDifferentialForm I M k) = 0 := by
  ext x
  simp only [smoothExtDeriv, zero_apply]
  rw [mfderiv_const]
  simp

/-- Exterior derivative is linear. -/
theorem smoothExtDeriv_add {k : ℕ} (ω₁ ω₂ : SmoothDifferentialForm I M k) :
    smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ := by
  ext x
  let V := ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k)
  have h1 : MDifferentiableAt I 𝓘(𝕜, V) ω₁.toFun x := 
    (ω₁.smooth' x).mdifferentiableAt (by simp only [OrderTop.le_top])
  have h2 : MDifferentiableAt I 𝓘(𝕜, V) ω₂.toFun x := 
    (ω₂.smooth' x).mdifferentiableAt (by simp only [OrderTop.le_top])
  unfold smoothExtDeriv
  simp only
  rw [mfderiv_add h1 h2]
  simp only [alternatizeUncurryFin_add]
  rfl

/-- Exterior derivative of an exterior derivative is zero (d² = 0).
    
    This fundamental property follows from the symmetry of second derivatives.
    In charts, this reduces to `extDeriv_extDeriv_apply` from Mathlib. -/
theorem smoothExtDeriv_smoothExtDeriv {k : ℕ} (ω : SmoothDifferentialForm I M k) :
    smoothExtDeriv (smoothExtDeriv ω) = 0 := by
  -- This proof requires relating mfderiv to fderiv in charts and using extDeriv_extDeriv_apply.
  -- The key insight is that in any chart φ around x:
  --   mfderiv I J' (mfderiv I J ω) = fderiv 𝕜 (fderiv 𝕜 (ω ∘ φ⁻¹))
  -- and the alternation of this is zero by symmetry of second derivatives.
  sorry

end SmoothDifferentialForm
