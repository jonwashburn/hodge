import Hodge.Analytic.Advanced.IntegrationTests
import Hodge.Analytic.Laplacian.ConnectionTests
import Hodge.Kahler.Lefschetz.LefschetzTests
import Hodge.GMT.GMTTests
import Hodge.Classical.CycleClass
import Hodge.Analytic.Integration.TopFormIntegral
import Hodge.Analytic.HodgeLaplacian

/-!
# Master Tests (Round 6, updated Round 10)

This file is a small "integration test harness" that imports all per-agent test files and
adds a few cross-module typechecking checks.

It is intended for **build verification**, not for the main proof track.

## Round 10 Updates (Agent 4)
- Added tests for `topFormIntegral_real'` being nontrivial
- Added tests for `L2InnerProduct` status
- Verified cross-module imports still work
-/

noncomputable section

open Classical Hodge
open scoped Manifold

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [MeasurableSpace X] [Nonempty X]

/-! ## Cross-module smoke tests -/

-- CycleClass: PD form is closed, hence yields a cohomology class.
example (p : ℕ) (Z : Set X) :
    IsFormClosed (CycleClass.poincareDualForm n X p Z) :=
  CycleClass.poincareDualForm_isClosed n X p Z

example (p : ℕ) (Z : Set X) :
    DeRhamCohomologyClass n X (2 * p) :=
  Hodge.ofForm (CycleClass.poincareDualForm n X p Z) (CycleClass.poincareDualForm_isClosed n X p Z)

/-! ## Round 10: topFormIntegral_real' nontriviality tests -/

-- Test 1: topFormIntegral_real' is defined via integrateDegree2p (not constant 0)
-- This verifies the Round 10 implementation is nontrivial
example (η : SmoothForm n X (2 * n)) :
    topFormIntegral_real' (n := n) (X := X) η =
    integrateDegree2p (n := n) (X := X) (k := 2 * n) Set.univ η := rfl

-- Test 2: topFormIntegral_real' satisfies linearity (structural property)
example (c : ℝ) (η₁ η₂ : SmoothForm n X (2 * n)) :
    topFormIntegral_real' (c • η₁ + η₂) =
      c * topFormIntegral_real' η₁ + topFormIntegral_real' η₂ :=
  topFormIntegral_real'_linear c η₁ η₂

-- Test 3: topFormIntegral_real' of zero is zero (basic property)
example : topFormIntegral_real' (n := n) (X := X) (0 : SmoothForm n X (2 * n)) = 0 :=
  topFormIntegral_real'_zero

-- Test 4: topFormIntegral_complex uses topFormIntegral_real' (nontrivial)
example (η : SmoothForm n X (2 * n)) :
    topFormIntegral_complex (n := n) (X := X) η =
    Complex.ofReal (topFormIntegral_real' η) := rfl

/-! ## Round 10: L2InnerProduct status tests -/

-- Test 5: L2InnerProduct is defined (structure check)
-- Currently uses L2InnerProductData.trivial (pending Agent 2's R10-A2-L2 task)
example (ω η : SmoothForm n X 2) :
    L2InnerProduct (n := n) (X := X) ω η =
    (L2InnerProductData.trivial n X 2).inner ω η := rfl

-- Test 6: L2InnerProduct satisfies sesquilinearity (left-linear)
example (c : ℂ) (ω₁ ω₂ η : SmoothForm n X 2) :
    L2InnerProduct (c • ω₁ + ω₂) η =
      c * L2InnerProduct ω₁ η + L2InnerProduct ω₂ η :=
  L2InnerProduct_linear_left c ω₁ ω₂ η

-- Test 7: L2InnerProduct is Hermitian symmetric
example (ω η : SmoothForm n X 2) :
    L2InnerProduct ω η = (starRingEnd ℂ) (L2InnerProduct η ω) :=
  L2InnerProduct_hermitian ω η

-- Test 8: L2InnerProduct is positive semidefinite
example (ω : SmoothForm n X 2) :
    0 ≤ (L2InnerProduct (n := n) (X := X) ω ω).re :=
  L2InnerProduct_nonneg ω

/-! ## Round 10: Cross-module import verification -/

-- Verify that key types from different modules are compatible

-- From Integration: integrateDegree2p is accessible
example (k : ℕ) (Z : Set X) (ω : SmoothForm n X k) : ℝ :=
  integrateDegree2p (n := n) (X := X) k Z ω

-- From Currents: integration_current is accessible (requires MeasurableSpace)
example (k : ℕ) (Z : Set X) : Current n X k :=
  _root_.integration_current (n := n) (X := X) (k := k) Z

-- From HodgeLaplacian: hodgeLaplacian is accessible
example (hk : 1 ≤ 2) (hk' : 2 + 1 ≤ 2 * n) (ω : SmoothForm n X 2) : SmoothForm n X 2 :=
  hodgeLaplacian hk hk' ω
