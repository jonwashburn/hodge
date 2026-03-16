import Hodge.WorkInProgress.GMT.EuclideanMollifier
import Hodge.WorkInProgress.GMT.EuclideanCurrentRegularization
import Hodge.WorkInProgress.Analytic.Pullback
import Hodge.WorkInProgress.GMT.CurrentPushforward
import Hodge.Analytic.Currents
import Hodge.Analytic.Forms
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section

open Classical Manifold
open scoped BigOperators

namespace Hodge.GMT

universe u

variable {n : ℕ} {X : Type u} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ}

/-! ### Local chart derivative as a fixed-type map -/
noncomputable def mfderivChartAt (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (i x : X) : TangentModel n →L[ℝ] TangentModel n :=
  mfderiv (𝓒_complex n) (𝓒_complex n) (chartAt (EuclideanSpace ℂ (Fin n)) i) x

/-- Data: a smooth partition of unity subordinate to chart sources (WIP). -/
class MollifierPartitionData (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Type (u + 1) where
  ρ : SmoothPartitionOfUnity X (𝓒_complex n) X (Set.univ : Set X)
  subordinate :
    ρ.IsSubordinate (fun x : X => (chartAt (EuclideanSpace ℂ (Fin n)) x).source)

/-! Data: a uniform bound on chart derivatives. -/
class ChartDerivBoundData (n : ℕ) (X : Type u) (k : ℕ) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Type (u + 1) where
  bound : X → ℝ
  bound_spec :
    ∀ (i x : X),
      ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k ≤ bound i

/-! Data: charts are smooth as global maps (WIP). -/
class ChartSmoothData (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Prop where
  contMDiff_chartAt : ∀ x : X, ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤
    (chartAt (EuclideanSpace ℂ (Fin n)) x)

/-! ### A concrete bound from compactness (WIP) -/

lemma mfderiv_chartAt_eq_tangentCoordChange_on_source
    [HasLocallyConstantCharts n X] (i x : X)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source) :
    mfderiv (𝓒_complex n) (𝓒_complex n)
        (chartAt (EuclideanSpace ℂ (Fin n)) i) x =
      tangentCoordChange (I := 𝓒_complex n) i i x := by
  have hmf :
      mfderiv (𝓒_complex n) (𝓒_complex n)
          (chartAt (EuclideanSpace ℂ (Fin n)) i) x =
        tangentCoordChange (I := 𝓒_complex n) x i x := by
    simpa using
      (mfderiv_chartAt_eq_tangentCoordChange (I := 𝓒_complex n)
        (H := EuclideanSpace ℂ (Fin n)) (x := x) (y := i) hx)
  have hchart :
      chartAt (EuclideanSpace ℂ (Fin n)) x =
        chartAt (EuclideanSpace ℂ (Fin n)) i :=
    (HasLocallyConstantCharts.hCharts (n := n) (X := X) (x := i) (y := x) hx)
  have hachart :
      achart (EuclideanSpace ℂ (Fin n)) x =
        achart (EuclideanSpace ℂ (Fin n)) i := by
    apply Subtype.ext
    simpa [achart_def] using hchart
  have hcoord :
      tangentCoordChange (I := 𝓒_complex n) x i =
        tangentCoordChange (I := 𝓒_complex n) i i := by
    funext z
    ext v
    simp [tangentCoordChange, hachart]
  have hcoord_x :
      tangentCoordChange (I := 𝓒_complex n) x i x =
        tangentCoordChange (I := 𝓒_complex n) i i x :=
    congrArg (fun f => f x) hcoord
  exact hmf.trans hcoord_x

lemma mfderiv_chartAt_continuousOn_source
    [HasLocallyConstantCharts n X] (i : X) :
    ContinuousOn
      (fun x => mfderivChartAt (n := n) (X := X) i x)
      (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
  refine
    (continuousOn_const :
        ContinuousOn (fun _ : X => ContinuousLinearMap.id ℝ (TangentModel n))
          (chartAt (EuclideanSpace ℂ (Fin n)) i).source).congr ?_
  intro x hx
  have hx' : x ∈ (extChartAt (𝓒_complex n) i).source := by
    simpa [extChartAt_source] using hx
  have hself :
      tangentCoordChange (I := 𝓒_complex n) i i x =
        ContinuousLinearMap.id ℝ (TangentModel n) := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    exact tangentCoordChange_self (I := 𝓒_complex n) (x := i) (z := x) (v := v) hx'
  have hmf :
      mfderivChartAt (n := n) (X := X) i x =
        tangentCoordChange (I := 𝓒_complex n) i i x := by
    simpa [mfderivChartAt] using
      (mfderiv_chartAt_eq_tangentCoordChange_on_source (n := n) (X := X) i x hx)
  show mfderivChartAt n X i x = ContinuousLinearMap.id ℝ (TangentModel n)
  exact hmf.trans hself

lemma mfderiv_chartAt_norm_pow_continuousOn_source
    [HasLocallyConstantCharts n X] (i : X) :
    ContinuousOn
      (fun x =>
        ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k)
      (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
  have hcont := mfderiv_chartAt_continuousOn_source (n := n) (X := X) i
  exact (hcont.norm.pow _)

noncomputable def chartDerivBound (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (i : X) : ℝ :=
  sSup (Set.range fun x =>
    ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k)

lemma mfderivChartAt_eq_id [HasLocallyConstantCharts n X] (i x : X)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source) :
    mfderivChartAt (n := n) (X := X) i x = ContinuousLinearMap.id ℝ (TangentModel n) := by
  have hx' : x ∈ (extChartAt (𝓒_complex n) i).source := by
    simpa [extChartAt_source] using hx
  have hmf : mfderivChartAt (n := n) (X := X) i x =
      tangentCoordChange (I := 𝓒_complex n) i i x := by
    simpa [mfderivChartAt] using
      (mfderiv_chartAt_eq_tangentCoordChange_on_source (n := n) (X := X) i x hx)
  have hself : tangentCoordChange (I := 𝓒_complex n) i i x =
      ContinuousLinearMap.id ℝ (TangentModel n) := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    exact tangentCoordChange_self (I := 𝓒_complex n) (x := i) (z := x) (v := v) hx'
  exact hmf.trans hself

lemma mfderivChartAt_norm_pow_le_on_source [HasLocallyConstantCharts n X] (i x : X)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source) :
    ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k ≤
      ‖ContinuousLinearMap.id ℝ (TangentModel n)‖ ^ k := by
  rw [mfderivChartAt_eq_id (n := n) (X := X) i x hx]

instance instMollifierPartitionData_of_sigmaCompact [T2Space X] [SigmaCompactSpace X] :
    MollifierPartitionData n X := by
  classical
  classical
  choose ρ hρ using
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source (I := 𝓒_complex n) (M := X))
  exact { ρ := ρ, subordinate := hρ }

/-- Local chart-level mollification of a current (WIP). -/
def mollifyChart (ε : ℝ) (x₀ : X) (T : Current n X k)
    [ChartDerivBoundData n X k] [ChartSmoothData n X]
    [EuclideanCurrentRegularizationData n k] : SmoothForm n X k := by
  let f := chartAt (EuclideanSpace ℂ (Fin n)) x₀
  let C := ChartDerivBoundData.bound (n := n) (X := X) (k := k) x₀
  have hC :
      ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C := by
    intro x
    simpa [f] using (ChartDerivBoundData.bound_spec (n := n) (X := X) (k := k) x₀ x)
  have hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f :=
    (ChartSmoothData.contMDiff_chartAt (n := n) (X := X) x₀)
  let Tchart : ModelCurrent n k :=
    currentPushforward (n := n) (k := k) (f := f) C hC hf T
  let ωchart : SmoothForm n (TangentModel n) k :=
    regularizeCurrentEuclidean (n := n) (k := k) Tchart
  exact smoothFormPullback (n := n) (f := f) hf ωchart

/-- Weighted sum of chart-level mollifications using a partition of unity (WIP). -/
def mollifyWeighted (ε : ℝ) [MollifierPartitionData n X] [ChartDerivBoundData n X k]
    [ChartSmoothData n X] [EuclideanCurrentRegularizationData n k]
    (T : Current n X k) : SmoothForm n X k :=
  let ρ := (MollifierPartitionData.ρ (n := n) (X := X))
  { as_alternating := fun x =>
      Finset.sum (ρ.finsupport x) (fun i =>
        ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x)
    is_smooth := by
      classical
      have hcont_coe :
          ContMDiff (𝓒_complex n) 𝓘(ℝ, FiberAlt n k) (↑(⊤ : ℕ∞))
            (fun x =>
              ∑ᶠ i, ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x) := by
        refine SmoothPartitionOfUnity.contMDiff_finsum_smul
          (f := ρ) (g := fun i x =>
            (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x)
          (F := FiberAlt n k) (n := (⊤ : ℕ∞)) ?_
        intro i x _
        exact (mollifyChart (n := n) (X := X) (k := k) ε i T).smooth.contMDiffAt
      have h_eq :
          (fun x =>
            Finset.sum (ρ.finsupport x) (fun i =>
              ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x)) =
          (fun x =>
            ∑ᶠ i, ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x) := by
        funext x
        simpa using
          (SmoothPartitionOfUnity.sum_finsupport_smul_eq_finsum (ρ := ρ) (x₀ := x)
            (φ := fun i x => (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x))
      change ContMDiff (𝓒_complex n) 𝓘(ℝ, FiberAlt n k) formSmoothness _
      rw [h_eq]
      simpa [formSmoothness] using hcont_coe }

/-- Manifold mollifier: patch Euclidean mollifiers with a partition of unity (WIP). -/
def mollifyManifold (ε : ℝ) [MollifierPartitionData n X] [ChartDerivBoundData n X k]
    [ChartSmoothData n X] [EuclideanCurrentRegularizationData n k]
    (T : Current n X k) : SmoothForm n X k :=
  mollifyWeighted (n := n) (X := X) (k := k) ε T

end Hodge.GMT

section TangentModelInstance

open Hodge Hodge.GMT

variable {n : ℕ} {k : ℕ}

noncomputable instance Hodge.GMT.instChartDerivBoundData_TangentModel :
    Hodge.GMT.ChartDerivBoundData n (TangentModel n) k where
  bound _ := ‖ContinuousLinearMap.id ℝ (TangentModel n)‖ ^ k
  bound_spec := by
    intro i x
    have hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by simp
    have hx' : x ∈ (extChartAt (𝓒_complex n) i).source := by simp [extChartAt_source]
    have hid : Hodge.GMT.mfderivChartAt (n := n) (X := TangentModel n) i x =
        ContinuousLinearMap.id ℝ (TangentModel n) := by
      unfold Hodge.GMT.mfderivChartAt
      rw [mfderiv_chartAt_eq_tangentCoordChange (I := 𝓒_complex n) (by simpa using hx)]
      refine ContinuousLinearMap.ext (fun v => ?_)
      have := tangentCoordChange_self (I := 𝓒_complex n) (x := x) (z := x) (v := v) hx'
      simpa [TangentSpace] using this
    rw [hid]

end TangentModelInstance
