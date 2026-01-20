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
  [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]

/-! ## Basic smoke tests -/

-- Test 1: integration current of empty set is zero (codimension form).
example (p : ℕ) :
    integrationCurrent (n := n) (X := X) p (∅ : Set X) = (0 : DeRhamCurrent n X (2 * p)) :=
  integrationCurrent_empty (n := n) (X := X) p

-- Test 2: linearity of evaluation for integration currents.
example (p : ℕ) (Z : Set X) (c : ℝ) (ω₁ ω₂ : SmoothForm n X (2 * p)) :
    (integrationCurrent (n := n) (X := X) p Z).toFun (c • ω₁ + ω₂) =
      c * (integrationCurrent (n := n) (X := X) p Z).toFun ω₁ +
        (integrationCurrent (n := n) (X := X) p Z).toFun ω₂ :=
  integrationCurrent_linear (n := n) (X := X) (p := p) (Z := Z) c ω₁ ω₂

-- Test 3: boundary operator typechecks.
example {k : ℕ} (T : DeRhamCurrent n X k) : DeRhamCurrent n X (k - 1) :=
  DeRhamCurrent.boundary (n := n) (X := X) (k := k) T

-- Test 4: real-valued flat norm is nonnegative.
example {k : ℕ} (T : Current n X k) :
    0 ≤ _root_.flatNorm (n := n) (X := X) (k := k) T :=
  _root_.flatNorm_nonneg (n := n) (X := X) (k := k) T

-- Test 5: Poincaré dual form constructor typechecks.
example (p : ℕ) (Z : Set X) : SmoothForm n X (2 * p) :=
  poincareDualForm_construct (n := n) (X := X) (p := p) Z

/-! ## Round 7 Tests: Current Architecture -/

-- Test 6: integration_current uses closedSubmanifold (depends on Z)
-- The current's carrier is Z, not empty.
example (k : ℕ) (Z : Set X) :
    (IntegrationData.closedSubmanifold n X k Z).carrier = Z := rfl

-- Test 7: setIntegral is currently the constant-0 stub
-- (Agent 4 owns upgrading this once measure layer is non-degenerate)
example (k : ℕ) (Z : Set X) (ω : SmoothForm n X k) :
    setIntegral (n := n) (X := X) k Z ω = 0 := rfl

-- Test 8: integration current of a set Z uses setIntegral
-- (This is the key Round 7 deliverable: currents now depend on Z via closedSubmanifold)
example (k : ℕ) (Z : Set X) (ω : SmoothForm n X k) :
    (integrationCurrentK (n := n) (X := X) k Z).toFun ω = setIntegral k Z ω := rfl

-- Test 9: The carrier of a closedSubmanifold IntegrationData is the set itself
example (k : ℕ) (Z₁ Z₂ : Set X) (hne : Z₁ ≠ Z₂) :
    (IntegrationData.closedSubmanifold n X k Z₁).carrier ≠
    (IntegrationData.closedSubmanifold n X k Z₂).carrier := by
  simp only [IntegrationData.closedSubmanifold]
  exact hne
