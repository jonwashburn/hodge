import Hodge.WorkInProgress.GMT.EuclideanMollifier
import Hodge.WorkInProgress.GMT.LocalCurrents

noncomputable section

namespace Hodge.GMT

variable {n : ℕ} {k : ℕ}

open Classical
open scoped BigOperators

/-- A real basis of the Euclidean model fiber of `k`-forms. -/
noncomputable def modelFiberBasis :
    Module.Basis (Fin (Module.finrank ℝ (FiberAlt n k))) ℝ (FiberAlt n k) :=
  Module.finBasis ℝ (FiberAlt n k)

/-- The shifted Euclidean bump is smooth in the spatial variable. -/
theorem shifted_bump_contDiff (ε : ℝ) (hε : ε ≠ 0) (x : TangentModel n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y) := by
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => bumpBaseFun (E := TangentModel n) z) := by
    simpa [bumpBaseFun] using (bumpBase (E := TangentModel n)).contDiff (n := (⊤ : ℕ∞))
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => ε⁻¹ • z) :=
    (contDiff_const_smul (c := ε⁻¹)).comp contDiff_id
  have hbump : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => bump (E := TangentModel n) ε z) := by
    simpa [bump] using hbase.comp hscale
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun y : TangentModel n => x - y) := by
    simpa using contDiff_const.sub contDiff_id
  simpa [shifted_bump] using hbump.comp hsub

/-- The shifted Euclidean bump is compactly supported in the spatial variable. -/
theorem shifted_bump_hasCompactSupport (ε : ℝ) (hε : ε ≠ 0) (x : TangentModel n) :
    HasCompactSupport (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y) := by
  have hbase : HasCompactSupport (fun z : TangentModel n => bumpBaseFun (E := TangentModel n) z) := by
    simpa [bumpBaseFun] using (bumpBase (E := TangentModel n)).hasCompactSupport
  have hbump : HasCompactSupport (fun z : TangentModel n => bump (E := TangentModel n) ε z) := by
    simpa [bump] using hbase.comp_smul (inv_ne_zero hε)
  have hsub :
      Topology.IsClosedEmbedding (fun y : TangentModel n => x - y) := by
    simpa [sub_eq_add_neg, Function.comp] using
      (Topology.IsClosedEmbedding.comp
        (hg := (Homeomorph.addLeft x).isClosedEmbedding)
        (hf := (Homeomorph.neg (G := TangentModel n)).isClosedEmbedding))
  simpa [shifted_bump, Function.comp] using hbump.comp_isClosedEmbedding hsub

/-- Fixed-bump test form centered at `x` with fiber coefficient `A`. -/
noncomputable def shiftedBumpTestForm (ε : ℝ) (hε : ε ≠ 0)
    (x : TangentModel n) (A : FiberAlt n k) : Hodge.TestForm n (TangentModel n) k :=
  ⟨{ as_alternating := fun y => shifted_bump (E := TangentModel n) ε x y • A
    , is_smooth := by
        have hscalar := shifted_bump_contDiff (n := n) ε hε x
        have hsmul :
            ContDiff ℝ (⊤ : ℕ∞)
              (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y • A) := by
          simpa using hscalar.smul contDiff_const
        show IsSmoothAlternating n (TangentModel n) k
          (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y • A)
        unfold IsSmoothAlternating 𝓒_complex TangentModel
        convert hsmul.contMDiff using 1 <;> simp [formSmoothness]
    }
    , by
        have hscalar :
            HasCompactSupport (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y) :=
          shifted_bump_hasCompactSupport (n := n) ε hε x
        have hcoeff :
            HasCompactSupport
              ((fun r : ℝ => r • A) ∘ (fun y : TangentModel n => shifted_bump (E := TangentModel n) ε x y)) :=
          HasCompactSupport.comp_left hscalar (by
            ext r
            simp)
        simpa [Function.comp] using hcoeff ⟩

/-- The explicit Euclidean smoothing formula before proving the result is a `SmoothForm`. -/
noncomputable def regularizeModelCurrentRaw (ε : ℝ) (hε : ε ≠ 0)
    (T : ModelCurrent n k) : TangentModel n → FiberAlt n k :=
  fun x =>
    let b := modelFiberBasis (n := n) (k := k)
    ∑ i, (T.toContinuousLinearMap (shiftedBumpTestForm (n := n) (k := k) ε hε x (b i))) • b i

/-- The fixed-scale raw Euclidean smoothing formula used by the manifold mollifier. -/
noncomputable def regularizeModelCurrentRawUnit (T : ModelCurrent n k) :
    TangentModel n → FiberAlt n k :=
  regularizeModelCurrentRaw (n := n) (k := k) (ε := 1) (by norm_num) T

/-- The shifted bump is jointly smooth in the center parameter `x` and the spatial variable `y`.
This is the key ingredient for proving smooth dependence of `regularizeModelCurrentRaw` on `x`. -/
theorem shifted_bump_contDiff_joint (ε : ℝ) (hε : ε ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : TangentModel n × TangentModel n =>
      shifted_bump (E := TangentModel n) ε p.1 p.2) := by
  have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => bumpBaseFun (E := TangentModel n) z) := by
    simpa [bumpBaseFun] using (bumpBase (E := TangentModel n)).contDiff (n := (⊤ : ℕ∞))
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => ε⁻¹ • z) :=
    (contDiff_const_smul (c := ε⁻¹)).comp contDiff_id
  have hbump : ContDiff ℝ (⊤ : ℕ∞) (fun z : TangentModel n => bump (E := TangentModel n) ε z) := by
    simpa [bump] using hbase.comp hscale
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun p : TangentModel n × TangentModel n => p.1 - p.2) := by
    exact contDiff_fst.sub contDiff_snd
  simpa [shifted_bump] using hbump.comp hsub

/-- The smoothness of `x ↦ regularizeModelCurrentRaw ε hε T x`.
This follows from joint smoothness of the bump function and continuity of `T`. -/
theorem regularizeModelCurrentRaw_isSmooth (ε : ℝ) (hε : ε ≠ 0)
    (T : ModelCurrent n k) :
    IsSmoothAlternating n (TangentModel n) k (regularizeModelCurrentRaw (n := n) (k := k) ε hε T) := by
  unfold regularizeModelCurrentRaw
  unfold IsSmoothAlternating 𝓒_complex TangentModel
  simp only
  sorry

/-- Package the raw Euclidean smoothing formula as a `SmoothForm`. -/
noncomputable def regularizeModelCurrentSmoothForm (ε : ℝ) (hε : ε ≠ 0)
    (T : ModelCurrent n k) : SmoothForm n (TangentModel n) k :=
  ⟨regularizeModelCurrentRaw (n := n) (k := k) ε hε T,
    regularizeModelCurrentRaw_isSmooth (n := n) (k := k) ε hε T⟩

/-- Honest Euclidean regularization interface on chart-model currents. -/
class EuclideanCurrentRegularizationData (n : ℕ) (k : ℕ) : Type where
  regularize : ModelCurrent n k → SmoothForm n (TangentModel n) k

/-- Concrete `EuclideanCurrentRegularizationData` instance using bump-function convolution. -/
noncomputable instance instEuclideanCurrentRegularizationData :
    EuclideanCurrentRegularizationData n k where
  regularize := fun T => regularizeModelCurrentSmoothForm (n := n) (k := k) 1 (by norm_num) T

/-- Regularize a current on the Euclidean model space (WIP). -/
noncomputable def regularizeCurrentEuclidean
    [EuclideanCurrentRegularizationData n k]
    (T : ModelCurrent n k) : SmoothForm n (TangentModel n) k :=
  EuclideanCurrentRegularizationData.regularize (n := n) (k := k) T

end Hodge.GMT
