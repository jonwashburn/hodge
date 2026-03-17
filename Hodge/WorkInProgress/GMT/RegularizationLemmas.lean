import Hodge.GMT.RegularizationLemmas

noncomputable section

open Classical Hodge

namespace Hodge.GMT

/-
`CurrentRegularizationLemmas` is now derivable from the stronger companion
interface `CurrentRegularizationLaws`, so this WIP file no longer needs to
invent a placeholder instance.

Zero-preservation is now in place on the WIP side:

* `currentPushforward_zero`
* `regularizeModelCurrentSmoothForm_zero`
* `mollifyChart_zero`
* `mollifyWeighted_zero`
* `mollify_zero`

and chart-level closedness is reduced to the Euclidean law package:

* `currentPushforward_isCycleAt`
* `mollifyChart_isClosed_of_isCycleAt`
* `mollifyWeighted_isClosed_of_isCycleAt`
* `mollify_isClosed_of_isCycleAt`

The partition-of-unity gluing blocker is now gone: `mollifyWeighted` no longer
uses weighted patching of different local regularizations. Instead, the global
form is defined pointwise from `mollifyChart ε x T`, and the proof shows it is
locally equal on each chart source to a single fixed chart mollifier.

The remaining honest blocker has moved back to the Euclidean/model layer:

* `MollifierRegularization.lean` now derives a global
  `CurrentRegularizationLaws` instance from `EuclideanCurrentRegularizationLaws`.
* But there is still no concrete proof of
  `EuclideanCurrentRegularizationLaws` for the bump-function regularizer.
* And the proof-track route still depends on WIP `ChartSmoothData` /
  `ChartDerivBoundData` scaffolding, which is not yet provided as an honest
  global instance for arbitrary projective Kähler manifolds.

Once that is done, the generic derivation in
`Hodge/GMT/RegularizationLemmas.lean` will automatically supply
`CurrentRegularizationLemmas` and hence `PoincareDualityFromCurrentsData`.
-/

end Hodge.GMT
