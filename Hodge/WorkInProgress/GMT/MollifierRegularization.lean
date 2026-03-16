import Hodge.GMT.HeatKernelRegularization
import Hodge.WorkInProgress.GMT.ManifoldMollifier
import Hodge.WorkInProgress.GMT.RegularizationLemmas

noncomputable section

open Classical Hodge

namespace Hodge.GMT

variable {n : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]
  [MollifierPartitionData n X]
variable {k : ℕ}
variable [ChartDerivBoundData n X k] [ChartSmoothData n X]
  [EuclideanCurrentRegularizationData n k]

/-- Mollifier regularization built from the manifold patching layer. -/
def mollify (ε : ℝ) (T : Current n X k) : SmoothForm n X k :=
  mollifyManifold (n := n) (X := X) (k := k) ε T

/-- Heat-kernel parameters (placeholder: fixed time = 1). -/
def heatKernelParams : HeatKernelParams := { time := 1, time_pos := Real.zero_lt_one }

instance instCurrentRegularizationData : CurrentRegularizationData n X k where
  regularize := fun T => mollify (n := n) (X := X) (k := k) 1 T

instance instHeatKernelRegularizationData : HeatKernelRegularizationData n X k where
  params := heatKernelParams

end Hodge.GMT
