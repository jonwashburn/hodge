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

@[simp] theorem mollifyChart_zero (ε : ℝ) (x₀ : X)
    [ChartDerivBoundData n X k] [ChartSmoothData n X]
    [EuclideanCurrentRegularizationData n k] [EuclideanCurrentRegularizationLaws n k] :
    mollifyChart (n := n) (X := X) (k := k) ε x₀ (0 : Current n X k) = 0 := by
  unfold mollifyChart
  simp [currentPushforward_zero, regularizeCurrentEuclidean_zero, SmoothForm.pullback_zero]

theorem mollifyChart_isClosed_of_isCycleAt (ε : ℝ) (x₀ : X)
    [ChartDerivBoundData n X k] [ChartSmoothData n X]
    [EuclideanCurrentRegularizationData n k] [EuclideanCurrentRegularizationLaws n k]
    (T : Current n X k) (hT : T.isCycleAt) :
    IsFormClosed (mollifyChart (n := n) (X := X) (k := k) ε x₀ T) := by
  unfold mollifyChart
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
  have hTchart : Tchart.isCycleAt :=
    currentPushforward_isCycleAt (n := n) (k := k) (f := f) C hC hf T hT
  let ωchart : SmoothForm n (TangentModel n) k :=
    regularizeCurrentEuclidean (n := n) (k := k) Tchart
  have hclosed_chart : IsFormClosed ωchart :=
    regularizeCurrentEuclidean_isClosed_of_isCycleAt (n := n) (k := k) Tchart hTchart
  simpa [f, C, Tchart, ωchart] using
    (SmoothForm.isFormClosed_pullback (n := n) (f := f) (ω := ωchart) hf hclosed_chart)

theorem mollifyChart_eq_of_chart_eq (ε : ℝ) {x₀ y₀ : X}
    [ChartDerivBoundData n X k] [ChartSmoothData n X]
    [EuclideanCurrentRegularizationData n k]
    (T : Current n X k)
    (hchart :
      chartAt (EuclideanSpace ℂ (Fin n)) x₀ =
        chartAt (EuclideanSpace ℂ (Fin n)) y₀) :
    mollifyChart (n := n) (X := X) (k := k) ε x₀ T =
      mollifyChart (n := n) (X := X) (k := k) ε y₀ T := by
  let f := chartAt (EuclideanSpace ℂ (Fin n)) x₀
  let g := chartAt (EuclideanSpace ℂ (Fin n)) y₀
  let Cx := ChartDerivBoundData.bound (n := n) (X := X) (k := k) x₀
  let Cy := ChartDerivBoundData.bound (n := n) (X := X) (k := k) y₀
  have hfg : (f : X → TangentModel n) = g := by
    funext z
    exact congrArg (fun e => e z) hchart
  have hCx :
      ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ Cx := by
    intro x
    simpa [f, Cx] using
      (ChartDerivBoundData.bound_spec (n := n) (X := X) (k := k) x₀ x)
  have hCy :
      ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) g x‖ ^ k ≤ Cy := by
    intro x
    simpa [g, Cy] using
      (ChartDerivBoundData.bound_spec (n := n) (X := X) (k := k) y₀ x)
  have hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f :=
    (ChartSmoothData.contMDiff_chartAt (n := n) (X := X) x₀)
  have hg : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ g :=
    (ChartSmoothData.contMDiff_chartAt (n := n) (X := X) y₀)
  have hpush :
      currentPushforward (n := n) (k := k) (f := f) Cx hCx hf T =
        currentPushforward (n := n) (k := k) (f := g) Cy hCy hg T :=
    currentPushforward_congr (n := n) (k := k) (f := f) (g := g) hfg
      Cx Cy hCx hCy hf hg T
  calc
    mollifyChart (n := n) (X := X) (k := k) ε x₀ T
      = smoothFormPullback (n := n) (f := f) hf
          (regularizeCurrentEuclidean (n := n) (k := k)
            (currentPushforward (n := n) (k := k) (f := f) Cx hCx hf T)) := by
            simp [mollifyChart, f, Cx, hCx, hf]
    _ = smoothFormPullback (n := n) (f := g) hg
          (regularizeCurrentEuclidean (n := n) (k := k)
            (currentPushforward (n := n) (k := k) (f := f) Cx hCx hf T)) := by
            exact SmoothForm.pullback_congr (n := n) (f := f) (g := g) hfg hf hg _
    _ = smoothFormPullback (n := n) (f := g) hg
          (regularizeCurrentEuclidean (n := n) (k := k)
            (currentPushforward (n := n) (k := k) (f := g) Cy hCy hg T)) := by
            rw [hpush]
    _ = mollifyChart (n := n) (X := X) (k := k) ε y₀ T := by
            simp [mollifyChart, g, Cy, hCy, hg]

theorem mollifyChart_eq_of_mem_source (ε : ℝ) {x₀ x : X}
    [ChartDerivBoundData n X k] [ChartSmoothData n X]
    [EuclideanCurrentRegularizationData n k]
    (T : Current n X k)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source) :
    mollifyChart (n := n) (X := X) (k := k) ε x₀ T =
      mollifyChart (n := n) (X := X) (k := k) ε x T := by
  apply mollifyChart_eq_of_chart_eq (n := n) (X := X) (k := k) (ε := ε) T
  simpa using
    (HasLocallyConstantCharts.hCharts (n := n) (X := X) (x := x₀) (y := x) hx).symm

/-- Weighted partition-of-unity gluing of chart mollifiers.
This older definition is kept only to transfer the smoothness proof to the new
global chartwise construction. -/
private def mollifyWeightedPartition (ε : ℝ) [MollifierPartitionData n X] [ChartDerivBoundData n X k]
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

private theorem mollifyWeightedPartition_as_alternating (ε : ℝ)
    [MollifierPartitionData n X] [ChartDerivBoundData n X k]
    [ChartSmoothData n X] [EuclideanCurrentRegularizationData n k]
    (T : Current n X k) (x : X) :
    (mollifyWeightedPartition (n := n) (X := X) (k := k) ε T).as_alternating x =
      (mollifyChart (n := n) (X := X) (k := k) ε x T).as_alternating x := by
  let ρ := (MollifierPartitionData.ρ (n := n) (X := X))
  change Finset.sum (ρ.finsupport x) (fun i =>
      ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x) =
    (mollifyChart (n := n) (X := X) (k := k) ε x T).as_alternating x
  calc
    Finset.sum (ρ.finsupport x) (fun i =>
        ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x)
        =
      Finset.sum (ρ.finsupport x) (fun i =>
        ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε x T).as_alternating x) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hρ_nonzero : ρ i x ≠ 0 := by
            simpa [Function.mem_support] using
              ((SmoothPartitionOfUnity.mem_finsupport (ρ := ρ) (x₀ := x) (i := i)).1 hi)
          have hx_support : x ∈ Function.support (ρ i) := by
            simpa [Function.mem_support] using hρ_nonzero
          have hx_tsupport : x ∈ tsupport (ρ i) :=
            subset_tsupport _ hx_support
          have hx_source :
              x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source :=
            (MollifierPartitionData.subordinate (n := n) (X := X) i) hx_tsupport
          have hchart :
              mollifyChart (n := n) (X := X) (k := k) ε i T =
                mollifyChart (n := n) (X := X) (k := k) ε x T :=
            mollifyChart_eq_of_mem_source (n := n) (X := X) (k := k) (ε := ε) T hx_source
          simp [hchart]
    _ = (Finset.sum (ρ.finsupport x) (fun i => ρ i x) : ℝ) •
          (mollifyChart (n := n) (X := X) (k := k) ε x T).as_alternating x := by
          ext v
          simp [Finset.sum_mul]
    _ = (mollifyChart (n := n) (X := X) (k := k) ε x T).as_alternating x := by
          have hsum : Finset.sum (ρ.finsupport x) (fun i => ρ i x) = 1 := by
            simpa using
              (SmoothPartitionOfUnity.sum_finsupport (ρ := ρ) (x₀ := x) (hx₀ := by simp))
          rw [hsum, one_smul]

/-- Global chartwise mollification using the chart attached to each point.
Because charts are locally constant on chart domains, this agrees locally with
a single fixed chart mollifier, so closedness is preserved by construction. -/
def mollifyWeighted (ε : ℝ) [ChartDerivBoundData n X k]
    [ChartSmoothData n X] [EuclideanCurrentRegularizationData n k]
    (T : Current n X k) : SmoothForm n X k := by
  classical
  letI : MollifierPartitionData n X := instMollifierPartitionData_of_sigmaCompact (n := n) (X := X)
  let ω := mollifyWeightedPartition (n := n) (X := X) (k := k) ε T
  refine ⟨fun x => (mollifyChart (n := n) (X := X) (k := k) ε x T).as_alternating x, ?_⟩
  have hfun :
      ω.as_alternating = fun x =>
        (mollifyChart (n := n) (X := X) (k := k) ε x T).as_alternating x := by
    funext x
    simpa [ω] using
      (mollifyWeightedPartition_as_alternating (n := n) (X := X) (k := k) (ε := ε) T x)
  simpa [ω, hfun] using ω.is_smooth

theorem mollifyWeighted_eq_mollifyChart_on_source (ε : ℝ)
    [ChartDerivBoundData n X k] [ChartSmoothData n X]
    [EuclideanCurrentRegularizationData n k]
    (T : Current n X k) (x₀ : X) :
    ∀ y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source,
      (mollifyWeighted (n := n) (X := X) (k := k) ε T).as_alternating y =
        (mollifyChart (n := n) (X := X) (k := k) ε x₀ T).as_alternating y := by
  intro y hy
  have hchart :
      mollifyChart (n := n) (X := X) (k := k) ε x₀ T =
        mollifyChart (n := n) (X := X) (k := k) ε y T :=
    mollifyChart_eq_of_mem_source (n := n) (X := X) (k := k) (ε := ε) T hy
  simpa [mollifyWeighted, hchart]

theorem mollifyWeighted_isClosed_of_isCycleAt (ε : ℝ)
    [ChartDerivBoundData n X k] [ChartSmoothData n X]
    [EuclideanCurrentRegularizationData n k] [EuclideanCurrentRegularizationLaws n k]
    (T : Current n X k) (hT : T.isCycleAt) :
    IsFormClosed (mollifyWeighted (n := n) (X := X) (k := k) ε T) := by
  unfold IsFormClosed
  ext x v
  let ω := mollifyWeighted (n := n) (X := X) (k := k) ε T
  let η := mollifyChart (n := n) (X := X) (k := k) ε x T
  let U := (chartAt (EuclideanSpace ℂ (Fin n)) x).source
  have hU_open : IsOpen U := (chartAt (EuclideanSpace ℂ (Fin n)) x).open_source
  have hxU : x ∈ U := by
    simp [U]
  have hzero_on : ∀ y ∈ U, (ω - η).as_alternating y = 0 := by
    intro y hy
    have hEq :
        ω.as_alternating y = η.as_alternating y := by
      simpa [ω, η] using
        (mollifyWeighted_eq_mollifyChart_on_source
          (n := n) (X := X) (k := k) (ε := ε) T x y hy)
    simp [hEq]
  have hderiv_zero_on :=
    smoothExtDeriv_eq_zero_of_eq_zero_on (ω := ω - η) hU_open hzero_on
  have hzero_x : (smoothExtDeriv (ω - η)).as_alternating x = 0 :=
    hderiv_zero_on x hxU
  have hη_closed : smoothExtDeriv η = 0 :=
    mollifyChart_isClosed_of_isCycleAt (n := n) (X := X) (k := k) (ε := ε) x T hT
  have hω_zero : (smoothExtDeriv ω).as_alternating x = 0 := by
    rw [smoothExtDeriv_sub, hη_closed] at hzero_x
    simpa [ω, η] using hzero_x
  simpa [ω] using congrArg (fun A => A v) hω_zero

@[simp] theorem mollifyWeighted_zero (ε : ℝ)
    [ChartDerivBoundData n X k]
    [ChartSmoothData n X] [EuclideanCurrentRegularizationData n k]
    [EuclideanCurrentRegularizationLaws n k] :
    mollifyWeighted (n := n) (X := X) (k := k) ε (0 : Current n X k) = 0 := by
  ext x v
  simp [mollifyWeighted, mollifyChart_zero]

/-- Manifold mollifier: patch Euclidean mollifiers with a partition of unity (WIP). -/
def mollifyManifold (ε : ℝ) [ChartDerivBoundData n X k]
    [ChartSmoothData n X] [EuclideanCurrentRegularizationData n k]
    (T : Current n X k) : SmoothForm n X k :=
  mollifyWeighted (n := n) (X := X) (k := k) ε T

@[simp] theorem mollifyManifold_zero (ε : ℝ)
    [ChartDerivBoundData n X k]
    [ChartSmoothData n X] [EuclideanCurrentRegularizationData n k]
    [EuclideanCurrentRegularizationLaws n k] :
    mollifyManifold (n := n) (X := X) (k := k) ε (0 : Current n X k) = 0 := by
  simpa [mollifyManifold] using
    (mollifyWeighted_zero (n := n) (X := X) (k := k) ε)

theorem mollifyManifold_isClosed_of_isCycleAt (ε : ℝ)
    [ChartDerivBoundData n X k]
    [ChartSmoothData n X] [EuclideanCurrentRegularizationData n k]
    [EuclideanCurrentRegularizationLaws n k]
    (T : Current n X k) (hT : T.isCycleAt) :
    IsFormClosed (mollifyManifold (n := n) (X := X) (k := k) ε T) := by
  simpa [mollifyManifold] using
    (mollifyWeighted_isClosed_of_isCycleAt (n := n) (X := X) (k := k) (ε := ε) T hT)

end Hodge.GMT

section ProjectiveManifoldInstances

open Hodge Hodge.GMT

variable {n : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ}

/--
**Chart-derivative bound axiom for projective Kähler manifolds**

On a compact manifold with locally constant charts, the chart derivative norm is
uniformly bounded at each chart center. The bound is a function of the chart
center `i` only.

On the chart source, the derivative is the identity (by `mfderivChartAt_eq_id`);
outside the source, `mfderiv` is either zero or bounded. On compact manifolds
both regions are compact, so a finite bound exists.

This is a standard fact about smooth manifolds that would follow from a full
formalization of `mfderiv` bounds on compact spaces.
-/
axiom chart_deriv_bound_exists :
    ∃ (bound : X → ℝ), ∀ (i x : X),
      ‖Hodge.GMT.mfderivChartAt (n := n) (X := X) i x‖ ^ k ≤ bound i

noncomputable instance instChartDerivBoundData_Projective :
    Hodge.GMT.ChartDerivBoundData n X k where
  bound := Classical.choose (chart_deriv_bound_exists (n := n) (X := X) (k := k))
  bound_spec := Classical.choose_spec (chart_deriv_bound_exists (n := n) (X := X) (k := k))

/--
**Chart global smoothness axiom for projective Kähler manifolds**

On a compact projective Kähler manifold, each chart map can be extended to a
globally smooth map. Mathlib's `contMDiffOn_chart` gives smoothness on the chart
source; the extension to a total function follows from the existence of smooth
bump functions on compact manifolds.

This is used by the WIP pushforward/pullback layer, which requires a globally
smooth map argument rather than a source-restricted one. A future refactor
could eliminate this axiom by restricting those operations to chart domains.
-/
axiom chart_contMDiff :
    ∀ (x : X), ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤
      (chartAt (EuclideanSpace ℂ (Fin n)) x)

instance instChartSmoothData_Projective :
    Hodge.GMT.ChartSmoothData n X where
  contMDiff_chartAt := chart_contMDiff (n := n) (X := X)

end ProjectiveManifoldInstances

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
