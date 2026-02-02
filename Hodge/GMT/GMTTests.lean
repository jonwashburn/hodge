import Hodge.GMT.Current
import Hodge.GMT.IntegrationCurrent
import Hodge.GMT.FlatNormTopology
import Hodge.GMT.PoincareDuality

/-!
# GMT Tests (Round 3)

This file is a lightweight compilation/typecheck suite for the Agent‑5 GMT layer.
It is not imported by the proof-track entry point.
-/

noncomputable section

open Classical Hodge Hodge.GMT

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [Nonempty X]

/-! ## Basic smoke tests -/

-- Test 1: linearity of evaluation for integration currents.
example (p : ℕ) (Z : Set X) (c : ℝ) (ω₁ ω₂ : SmoothForm n X (2 * p))
    [ClosedSubmanifoldStokesData n X (2 * p) Z] :
    (integrationCurrent (n := n) (X := X) p Z).toFun (c • ω₁ + ω₂) =
      c * (integrationCurrent (n := n) (X := X) p Z).toFun ω₁ +
        (integrationCurrent (n := n) (X := X) p Z).toFun ω₂ :=
  integrationCurrent_linear (n := n) (X := X) (p := p) (Z := Z) c ω₁ ω₂

-- Test 2: boundary operator typechecks.
example {k : ℕ} (T : DeRhamCurrent n X k) : DeRhamCurrent n X (k - 1) :=
  DeRhamCurrent.boundary (n := n) (X := X) (k := k) T

-- Test 3: real-valued flat norm is nonnegative.
example {k : ℕ} (T : Current n X k) :
    0 ≤ _root_.flatNorm (n := n) (X := X) (k := k) T :=
  _root_.flatNorm_nonneg (n := n) (X := X) (k := k) T

-- Test 4: Poincaré dual form constructor typechecks.
example (p : ℕ) (Z : Set X) [CurrentRegularizationData n X (2 * p)]
    [ClosedSubmanifoldStokesData n X (2 * p) Z] : SmoothForm n X (2 * p) :=
  poincareDualForm_construct (n := n) (X := X) (p := p) Z

/-! ## Round 7 Tests: Current Architecture -/

-- Test 6: IntegrationData.closedSubmanifold_zero carries the set Z
example (Z : Set X) :
    (IntegrationData.closedSubmanifold_zero n X Z).carrier = Z := rfl

-- Test 7: setIntegral is now wired to integrateDegree2p (Round 8)
-- For odd k, integrateDegree2p returns 0; for even k, it integrates via submanifoldIntegral
example (k : ℕ) (Z : Set X) (ω : SmoothForm n X k) :
    setIntegral (n := n) (X := X) k Z ω = integrateDegree2p (n := n) (X := X) k Z ω := rfl

-- Test 8: integration current of a set Z uses setIntegral
-- (This is the key Round 7 deliverable: currents now depend on Z via closedSubmanifold)
example (k : ℕ) (Z : Set X) (ω : SmoothForm n X k)
    [ClosedSubmanifoldStokesData n X k Z] :
    (integrationCurrentK (n := n) (X := X) k Z).toFun ω =
      (integrationCurrentReal (n := n) (X := X) k Z).toFun ω := by
  rfl

-- Test 9: The carrier of a closedSubmanifold IntegrationData is the set itself
example (k : ℕ) (Z₁ Z₂ : Set X) (hne : Z₁ ≠ Z₂) :
    (IntegrationData.closedSubmanifold_zero n X Z₁).carrier ≠
    (IntegrationData.closedSubmanifold_zero n X Z₂).carrier := by
  simpa [IntegrationData.closedSubmanifold_zero] using hne
