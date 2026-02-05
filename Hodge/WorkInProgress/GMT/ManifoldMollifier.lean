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

variable {n : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ}

/-- Data: a smooth partition of unity subordinate to chart sources (WIP). -/
class MollifierPartitionData (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Type where
  ρ : SmoothPartitionOfUnity X (𝓒_complex n) X univ
  subordinate :
    ρ.IsSubordinate (fun x : X => (chartAt (EuclideanSpace ℂ (Fin n)) x).source)

/-! Data: a uniform bound on chart derivatives (WIP). -/
class ChartDerivBoundData (n : ℕ) (X : Type*) (k : ℕ) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : Type where
  bound : X → ℝ
  bound_spec :
    ∀ (i x : X),
      ‖mfderiv (𝓒_complex n) (𝓒_complex n) (chartAt (EuclideanSpace ℂ (Fin n)) i) x‖ ^ k ≤ bound i

/-! ### A concrete bound from compactness (WIP) -/

lemma mfderiv_chartAt_eq_tangentCoordChange_on_source
    [HasLocallyConstantCharts n X] (i x : X)
    (hx : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source) :
    mfderiv (𝓒_complex n) (𝓒_complex n)
        (chartAt (EuclideanSpace ℂ (Fin n)) i) x =
      tangentCoordChange (I := 𝓒_complex n) i i x := by
  have hchart :
      chartAt (EuclideanSpace ℂ (Fin n)) x =
        chartAt (EuclideanSpace ℂ (Fin n)) i :=
    (HasLocallyConstantCharts.hCharts (n := n) (X := X) (x := i) (y := x) hx)
  -- Rewrite via the tangent coordinate change.
  have hmf :
      mfderiv (𝓒_complex n) (𝓒_complex n)
          (chartAt (EuclideanSpace ℂ (Fin n)) i) x =
        tangentCoordChange (I := 𝓒_complex n) x i x := by
    simpa using
      (mfderiv_chartAt_eq_tangentCoordChange (I := 𝓒_complex n)
        (H := EuclideanSpace ℂ (Fin n)) (x := x) (y := i) hx)
  -- If `chartAt x = chartAt i`, then the coordinate change uses the same chart.
  have hachart :
      achart (EuclideanSpace ℂ (Fin n)) x =
        achart (EuclideanSpace ℂ (Fin n)) i := by
    ext
    simpa [achart_def] using hchart
  have hcoord :
      tangentCoordChange (I := 𝓒_complex n) x i =
        tangentCoordChange (I := 𝓒_complex n) i i := by
    ext z v
    simp [tangentCoordChange, hachart]
  simpa [hcoord] using hmf

lemma mfderiv_chartAt_continuousOn_source
    [HasLocallyConstantCharts n X] (i : X) :
    ContinuousOn
      (fun x =>
        mfderiv (𝓒_complex n) (𝓒_complex n)
          (chartAt (EuclideanSpace ℂ (Fin n)) i) x)
      (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
  -- Reduce to the continuous tangent coordinate change.
  refine (continuousOn_tangentCoordChange (I := 𝓒_complex n) (x := i) (y := i)).congr ?_
  intro x hx
  -- `continuousOn_tangentCoordChange` is on the intersection of chart sources.
  have hx' :
      x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
    simpa [extChartAt_source] using hx
  simpa [extChartAt_source] using
    (mfderiv_chartAt_eq_tangentCoordChange_on_source (n := n) (X := X) i x hx')

lemma mfderiv_chartAt_norm_pow_continuousOn_source
    [HasLocallyConstantCharts n X] (i : X) :
    ContinuousOn
      (fun x =>
        ‖mfderiv (𝓒_complex n) (𝓒_complex n)
            (chartAt (EuclideanSpace ℂ (Fin n)) i) x‖ ^ k)
      (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
  have hcont :=
    (mfderiv_chartAt_continuousOn_source (n := n) (X := X) i)
  refine (ContinuousOn.pow ?_ _)
  exact hcont.norm

noncomputable def chartDerivBound (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (i : X) : ℝ :=
  sSup (Set.range fun x =>
    ‖mfderiv (𝓒_complex n) (𝓒_complex n) (chartAt (EuclideanSpace ℂ (Fin n)) i) x‖ ^ k)

lemma chartDerivBound_bddAbove (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] (i : X) :
    BddAbove (Set.range fun x =>
      ‖mfderiv (𝓒_complex n) (𝓒_complex n) (chartAt (EuclideanSpace ℂ (Fin n)) i) x‖ ^ k) := by
  -- TODO: show continuity of the derivative map for `chartAt`, then use compactness.
  -- Sketch: `contMDiffOn_chart` + `ContMDiffOn.continuousOn_tangentMapWithin` + zero section.
  sorry

lemma chartDerivBound_spec (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [CompactSpace X] (i x : X) :
    ‖mfderiv (𝓒_complex n) (𝓒_complex n) (chartAt (EuclideanSpace ℂ (Fin n)) i) x‖ ^ k ≤
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
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source (I := 𝓒_complex n) (M := X)
  exact { ρ := ρ, subordinate := hρ }

/-- Local chart-level mollification of a current (WIP). -/
def mollifyChart (ε : ℝ) (x₀ : X) (T : Current n X k)
    [ChartDerivBoundData n X k] : SmoothForm n X k := by
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
  let Tchart : Current n (TangentModel n) k :=
    currentPushforward (n := n) (k := k) (f := f) C hC T
  let ωchart : SmoothForm n (TangentModel n) k :=
    regularizeCurrentEuclidean (n := n) (k := k) Tchart
  exact smoothFormPullback (n := n) (f := f) ωchart

/-- Weighted sum of chart-level mollifications using a partition of unity (WIP). -/
def mollifyWeighted (ε : ℝ) [MollifierPartitionData n X] [ChartDerivBoundData n X k]
    (T : Current n X k) : SmoothForm n X k :=
  let ρ := (MollifierPartitionData.ρ (n := n) (X := X))
  { as_alternating := fun x =>
      ∑ i in ρ.finsupport x, ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x
    is_smooth := by
      classical
      -- Use the global `finsum` lemma for smooth partitions of unity, then rewrite to `finsupport`.
      have hcont :
          ContMDiff (𝓒_complex n) 𝓘(ℝ, FiberAlt n k) ⊤
            (fun x =>
              ∑ᶠ i, ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x) := by
        refine (SmoothPartitionOfUnity.contMDiff_finsum_smul (f := ρ) (n := (⊤)) ?_)
        intro i x hx
        -- Each chart-level mollification is a smooth form, hence smooth at every point.
        simpa using (mollifyChart (n := n) (X := X) (k := k) ε i T).smooth.contMDiffAt
      have h_eq :
          (fun x =>
            ∑ i in ρ.finsupport x,
              ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x) =
          (fun x =>
            ∑ᶠ i, ρ i x • (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x) := by
        funext x
        simpa using
          (SmoothPartitionOfUnity.sum_finsupport_smul_eq_finsum (ρ := ρ) (x₀ := x)
            (φ := fun i x => (mollifyChart (n := n) (X := X) (k := k) ε i T).as_alternating x))
      simpa [h_eq] using hcont }

/-- Manifold mollifier: patch Euclidean mollifiers with a partition of unity (WIP). -/
def mollifyManifold (ε : ℝ) [MollifierPartitionData n X] [ChartDerivBoundData n X k]
    (T : Current n X k) : SmoothForm n X k :=
  mollifyWeighted (n := n) (X := X) (k := k) ε T

end Hodge.GMT
