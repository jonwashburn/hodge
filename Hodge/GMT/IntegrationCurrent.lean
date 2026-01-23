import Hodge.GMT.Current

/-!
# GMT: Integration Currents (wrapper)

The project's current "integration current" implementation lives in
`Hodge.Analytic.Currents` as `integration_current`.

**Round 7 Update**: Now uses `IntegrationData.closedSubmanifold`, which:
- Carries Z in the `carrier` field (so the current depends on Z)
- Wires `integrate` to `setIntegral` (using Agent 3's Hausdorff infrastructure)
- Sets `bdryMass = 0` (closed submanifolds have no boundary)

The underlying integration uses `submanifoldIntegral`, which provides a nontrivial
stand-in formula using Hausdorff measure and form evaluation at a basepoint.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [Nonempty X]

/-- Integration current in degree `k` over a set `Z`.

Uses `IntegrationData.closedSubmanifold` with `setIntegral` wired to Agent 3's infrastructure. -/
noncomputable abbrev integrationCurrentK (k : ℕ) (Z : Set X) : DeRhamCurrent n X k :=
  _root_.integration_current (n := n) (X := X) (k := k) Z

/-- Integration current for a codimension parameter `p`, returning degree `2*p`.

This matches the signature used in `docs/OPERATIONAL_PLAN_5_AGENTS.md`. -/
noncomputable abbrev integrationCurrent (p : ℕ) (Z : Set X) : DeRhamCurrent n X (2 * p) :=
  integrationCurrentK (n := n) (X := X) (k := 2 * p) Z

/-- Integration current of the empty set is zero.
    (Hausdorff measure of empty set is 0, so submanifoldIntegral is 0.) -/
theorem integrationCurrentK_empty (k : ℕ) :
    integrationCurrentK (n := n) (X := X) k (∅ : Set X) = (0 : DeRhamCurrent n X k) := by
  ext ω
  -- closedSubmanifold uses setIntegral → integrateDegree2p → submanifoldIntegral → μ(∅) = 0
  unfold integrationCurrentK _root_.integration_current IntegrationData.toCurrent
    IntegrationData.closedSubmanifold
  simp only [Current.zero_toFun]
  -- Goal: setIntegral k ∅ ω = 0
  unfold setIntegral
  exact integrateDegree2p_empty k ω

/-- Integration current of the empty set is zero (codimension-form). -/
theorem integrationCurrent_empty (p : ℕ) :
    integrationCurrent (n := n) (X := X) p (∅ : Set X) = (0 : DeRhamCurrent n X (2 * p)) := by
  simpa [integrationCurrent] using (integrationCurrentK_empty (n := n) (X := X) (k := 2 * p))

/-- Linearity of the integration current evaluation (degree-`k` form). -/
theorem integrationCurrentK_linear (k : ℕ) (Z : Set X) (c : ℝ)
    (ω₁ ω₂ : SmoothForm n X k) :
    (integrationCurrentK (n := n) (X := X) k Z).toFun (c • ω₁ + ω₂) =
      c * (integrationCurrentK (n := n) (X := X) k Z).toFun ω₁ +
        (integrationCurrentK (n := n) (X := X) k Z).toFun ω₂ :=
  (integrationCurrentK (n := n) (X := X) k Z).is_linear c ω₁ ω₂

/-- Linearity of the integration current evaluation (codimension form, degree `2*p`). -/
theorem integrationCurrent_linear (p : ℕ) (Z : Set X) (c : ℝ)
    (ω₁ ω₂ : SmoothForm n X (2 * p)) :
    (integrationCurrent (n := n) (X := X) p Z).toFun (c • ω₁ + ω₂) =
      c * (integrationCurrent (n := n) (X := X) p Z).toFun ω₁ +
        (integrationCurrent (n := n) (X := X) p Z).toFun ω₂ :=
  (integrationCurrent (n := n) (X := X) p Z).is_linear c ω₁ ω₂

end Hodge.GMT
