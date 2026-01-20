import Hodge.GMT

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
