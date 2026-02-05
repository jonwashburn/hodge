import Hodge.WorkInProgress.GMT.EuclideanMollifier
import Hodge.WorkInProgress.GMT.EuclideanCurrentRegularization
import Hodge.WorkInProgress.Analytic.Pullback
import Hodge.WorkInProgress.GMT.CurrentPushforward
import Hodge.WorkInProgress.Instances.EuclideanManifold
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

/-! Data: a uniform bound on chart derivatives (WIP). -/
class ChartDerivBoundData (n : ℕ) (X : Type u) (k : ℕ) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Type (u + 1) where
  bound : X → ℝ
  bound_spec :
    ∀ (i x : X),
      ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k ≤
        bound i

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
  -- TODO: show `mfderiv` of `chartAt` agrees with the chart transition map
  -- using `HasLocallyConstantCharts`.
  sorry

lemma mfderiv_chartAt_continuousOn_source
    [HasLocallyConstantCharts n X] (i : X) :
    ContinuousOn
      (fun x => mfderivChartAt (n := n) (X := X) i x)
      (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
  -- TODO: prove continuity via `mfderiv_chartAt_eq_tangentCoordChange_on_source`
  -- and `continuousOn_tangentCoordChange`.
  sorry

lemma mfderiv_chartAt_norm_pow_continuousOn_source
    [HasLocallyConstantCharts n X] (i : X) :
    ContinuousOn
      (fun x =>
        ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k)
      (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
  -- TODO: combine `mfderiv_chartAt_continuousOn_source` with continuity of norms/powers.
  sorry

noncomputable def chartDerivBound (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (i : X) : ℝ :=
  sSup (Set.range fun x =>
    ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k)

lemma chartDerivBound_bddAbove (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] (i : X) :
    BddAbove (Set.range fun x =>
      ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k) := by
  -- TODO: show continuity of the derivative map for `chartAt`, then use compactness.
  -- Sketch: `contMDiffOn_chart` + `ContMDiffOn.continuousOn_tangentMapWithin` + zero section.
  sorry

lemma chartDerivBound_spec (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] (i x : X) :
    ‖mfderivChartAt (n := n) (X := X) i x‖ ^ k ≤
      chartDerivBound (n := n) (X := X) (k := k) i := by
  refine le_csSup (chartDerivBound_bddAbove (n := n) (X := X) (k := k) (i := i)) ?_
  exact ⟨x, rfl⟩

instance instChartDerivBoundData_of_compact {n : ℕ} {X : Type*} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] :
    ChartDerivBoundData n X k where
  bound := chartDerivBound (n := n) (X := X) (k := k)
  bound_spec := fun i x => chartDerivBound_spec (n := n) (X := X) (k := k) i x

instance instMollifierPartitionData_of_sigmaCompact [T2Space X] [SigmaCompactSpace X] :
    MollifierPartitionData n X := by
  classical
  classical
  choose ρ hρ using
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source (I := 𝓒_complex n) (M := X))
  exact { ρ := ρ, subordinate := hρ }

/-- Local chart-level mollification of a current (WIP). -/
def mollifyChart (ε : ℝ) (x₀ : X) (T : Current n X k)
    [ChartDerivBoundData n X k] [ChartSmoothData n X] : SmoothForm n X k := by
  -- TODO:
  -- 1. Pushforward `T` along the chart `chartAt x₀`.
  -- 2. Mollify the pushed-forward form in Euclidean space.
  -- 3. Pull back the mollified form along `chartAt x₀`.
  let f := chartAt (EuclideanSpace ℂ (Fin n)) x₀
  let C := ChartDerivBoundData.bound (n := n) (X := X) (k := k) x₀
  have hC :
      ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C := by
    intro x
    simpa [f] using (ChartDerivBoundData.bound_spec (n := n) (X := X) (k := k) x₀ x)
  have hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f :=
    (ChartSmoothData.contMDiff_chartAt (n := n) (X := X) x₀)
  let Tchart : Current n (TangentModel n) k :=
    currentPushforward (n := n) (k := k) (f := f) C hC hf T
  let ωchart : SmoothForm n (TangentModel n) k :=
    regularizeCurrentEuclidean (n := n) (k := k) Tchart
  exact smoothFormPullback (n := n) (f := f) ωchart

/-- Weighted sum of chart-level mollifications using a partition of unity (WIP). -/
def mollifyWeighted (ε : ℝ) [MollifierPartitionData n X] [ChartDerivBoundData n X k]
    [ChartSmoothData n X]
    (T : Current n X k) : SmoothForm n X k :=
  let ρ := (MollifierPartitionData.ρ (n := n) (X := X))
  { as_alternating := fun x =>
      Finset.sum (ρ.finsupport x) (fun i =>
        ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x)
    is_smooth := by
      -- TODO: prove smoothness using partition of unity and chart-level smoothness.
      sorry }

/-- Manifold mollifier: patch Euclidean mollifiers with a partition of unity (WIP). -/
def mollifyManifold (ε : ℝ) [MollifierPartitionData n X] [ChartDerivBoundData n X k]
    [ChartSmoothData n X]
    (T : Current n X k) : SmoothForm n X k :=
  mollifyWeighted (n := n) (X := X) (k := k) ε T

end Hodge.GMT
