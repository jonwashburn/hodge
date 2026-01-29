import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Stage 3 (seed): Mass / flat norm skeleton (off-proof-track)

This file is an **off-proof-track** seed for the plan in `tex/archive/HodgePlan-mc-28.1.26.rtf`.

We deliberately keep this file to *definitions only* (no `sorry`), so it can compile early while
Track A/Track B infrastructure is still being built.

The intended model is:
- a space of test forms `D` (later: an LF-space / locally convex space),
- a current `T` as a continuous linear functional `D →L[𝕜] 𝕜`,
- a (semi)norm on test forms controlling “comass ≤ 1”.

Downstream work will specialize this to the actual test-form spaces and prove the usual
inequalities.
-/

noncomputable section

namespace Hodge
namespace GMT
namespace Stage3

open scoped BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace 𝕜 D]

/-- Currents (seed model): continuous linear functionals on a normed space of test objects. -/
abbrev Current := D →L[𝕜] 𝕜

/-- Mass (seed): the operator norm of a current, i.e. `‖T‖ = sup_{‖ω‖ ≤ 1} ‖T ω‖`.

Later, `D` will be a test-form space equipped with the *comass* norm, and this will match the
GMT mass definition.
-/
noncomputable def mass (T : Current (D := D) (𝕜 := 𝕜)) : ℝ :=
  ‖T‖

/-- Flat norm (seed): placeholder definition.

Later, for currents `T = R + ∂S`, one defines `F(T) = inf (M(R) + M(S))`. Here we keep a minimal
skeleton that compiles without committing to a boundary operator yet.
-/
noncomputable def flatNorm (_T : Current (D := D) (𝕜 := 𝕜)) : ℝ :=
  0

end Stage3
end GMT
end Hodge
