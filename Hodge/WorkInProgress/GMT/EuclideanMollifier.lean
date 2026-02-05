import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.ConstMulAction

noncomputable section

open Classical MeasureTheory

namespace Hodge.GMT

section Local

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Base bump function on `E`. -/
def bumpBase : ContDiffBump (0 : E) :=
  { rIn := 1
    rOut := 2
    rIn_pos := Real.zero_lt_one
    rIn_lt_rOut := by norm_num }

/-- Standard bump function on `E`, scaled by ε. -/
def bump (ε : ℝ) (x : E) : ℝ :=
  bumpBase (ε⁻¹ • x)

/-- Shifted bump function: `y ↦ ρ_ε(x - y)`. -/
def shifted_bump (ε : ℝ) (x : E) (y : E) : ℝ :=
  bump ε (x - y)

/-- Euclidean mollifier (convolution with a bump). -/
def mollifyFunction (ε : ℝ) (f : E → ℝ) : E → ℝ :=
  fun x => ∫ y, bump ε (x - y) * f y ∂volume

/-- Smoothness of the Euclidean mollifier. -/
theorem mollifyFunction_contDiff (ε : ℝ) (f : E → ℝ) (hε : ε ≠ 0)
    (hf : LocallyIntegrable f (volume : Measure E)) :
    ContDiff ℝ ⊤ (mollifyFunction ε f) := by
  have hcompact : HasCompactSupport (fun x => bump (E := E) ε x) := by
    have hbase : HasCompactSupport (fun x => bumpBase (E := E) x) :=
      (ContDiffBump.hasCompactSupport (f := bumpBase (E := E)))
    simpa [bump] using hbase.comp_smul (inv_ne_zero hε)
  have hcont : ContDiff ℝ ⊤ (fun x => bump (E := E) ε x) := by
    -- `ContDiffBump` is smooth, and scaling is smooth.
    have hc : ContDiff ℝ ⊤ (fun _ : E => (0 : E)) := contDiff_const
    have hr : ContDiff ℝ ⊤ (fun _ : E => (bumpBase (E := E)).rIn) := contDiff_const
    have hR : ContDiff ℝ ⊤ (fun _ : E => (bumpBase (E := E)).rOut) := contDiff_const
    have hg : ContDiff ℝ ⊤ (fun x : E => ε⁻¹ • x) :=
      (contDiff_const_smul (c := ε⁻¹)).comp contDiff_id
    simpa [bump] using
      (ContDiff.contDiffBump (c := fun _ : E => (0 : E))
        (g := fun x : E => ε⁻¹ • x) (f := fun _ : E => bumpBase (E := E))
        hc hr hR hg)
  have hconv :
      ContDiff ℝ ⊤
        (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] fun x => bump (E := E) ε x) :=
    hcompact.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure E))
      hf hcont
  have hmollify :
      mollifyFunction (E := E) ε f =
        (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] fun x => bump (E := E) ε x) := by
    funext x
    simp [mollifyFunction, convolution_lsmul, smul_eq_mul, mul_comm]
  simpa [hmollify] using hconv

end Local

end Hodge.GMT
