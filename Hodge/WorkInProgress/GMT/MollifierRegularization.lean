import Hodge.GMT.HeatKernelRegularization
import Hodge.WorkInProgress.GMT.ManifoldMollifier
import Hodge.WorkInProgress.GMT.RegularizationLemmas

noncomputable section

open Classical Hodge

namespace Hodge.GMT

variable {n : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ}

/-- Mollifier regularization built from the manifold patching layer. -/
def mollify (ε : ℝ) (T : Current n X k) : SmoothForm n X k :=
  mollifyManifold (n := n) (X := X) (k := k) ε T

@[simp] theorem mollify_zero (ε : ℝ) :
    mollify (n := n) (X := X) (k := k) ε (0 : Current n X k) = 0 := by
  simpa [mollify] using
    (mollifyManifold_zero (n := n) (X := X) (k := k) ε)

theorem mollify_isClosed_of_isCycleAt (ε : ℝ)
    (T : Current n X k) (hT : T.isCycleAt) :
    IsFormClosed (mollify (n := n) (X := X) (k := k) ε T) := by
  simpa [mollify] using
    (mollifyManifold_isClosed_of_isCycleAt (n := n) (X := X) (k := k) (ε := ε) T hT)

/-- Heat-kernel parameters (placeholder: fixed time = 1). -/
def heatKernelParams : HeatKernelParams := { time := 1, time_pos := Real.zero_lt_one }

instance instCurrentRegularizationData : CurrentRegularizationData n X k where
  regularize := fun T => mollify (n := n) (X := X) (k := k) 1 T

instance instCurrentRegularizationLaws :
    CurrentRegularizationLaws n X k where
  regularize_isClosed_of_isCycleAt := by
    intro T hT
    change IsFormClosed (mollify (n := n) (X := X) (k := k) 1 T)
    exact mollify_isClosed_of_isCycleAt (n := n) (X := X) (k := k) (ε := 1) T hT
  regularize_zero := by
    change mollify (n := n) (X := X) (k := k) 1 (0 : Current n X k) = 0
    exact mollify_zero (n := n) (X := X) (k := k) (ε := 1)

instance instHeatKernelRegularizationData : HeatKernelRegularizationData n X k where
  params := heatKernelParams

end Hodge.GMT
