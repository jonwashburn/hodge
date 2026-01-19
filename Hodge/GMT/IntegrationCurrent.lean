import Hodge.GMT.Current

/-!
# GMT: Integration Currents (wrapper)

The project’s current “integration current” implementation lives in
`Hodge.Analytic.Currents` as `integration_current`.  At the moment it is implemented
via `IntegrationData.empty`, so it evaluates to `0` on all forms; this file provides
the module/name layout referenced in the operational plan.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]

/-- Integration current in degree `k` over a set `Z`.

This is currently the stub from `Hodge.Analytic.Currents` (implemented via `IntegrationData.empty`). -/
noncomputable abbrev integrationCurrentK (k : ℕ) (Z : Set X) : DeRhamCurrent n X k :=
  _root_.integration_current (n := n) (X := X) (k := k) Z

/-- Integration current for a codimension parameter `p`, returning degree `2*p`.

This matches the signature used in `docs/OPERATIONAL_PLAN_5_AGENTS.md`. -/
noncomputable abbrev integrationCurrent (p : ℕ) (Z : Set X) : DeRhamCurrent n X (2 * p) :=
  integrationCurrentK (n := n) (X := X) (k := 2 * p) Z

/-- Integration current of the empty set is zero. -/
theorem integrationCurrentK_empty (k : ℕ) :
    integrationCurrentK (n := n) (X := X) k (∅ : Set X) = (0 : DeRhamCurrent n X k) := by
  ext ω
  -- Everything is implemented via `IntegrationData.empty`, where `integrate := 0`.
  simp [integrationCurrentK, _root_.integration_current, IntegrationData.toCurrent, IntegrationData.empty,
    Current.zero_toFun]

/-- Integration current of the empty set is zero (codimension-form). -/
theorem integrationCurrent_empty (p : ℕ) :
    integrationCurrent (n := n) (X := X) p (∅ : Set X) = (0 : DeRhamCurrent n X (2 * p)) := by
  simpa [integrationCurrent] using (integrationCurrentK_empty (n := n) (X := X) (k := 2 * p))

end Hodge.GMT
