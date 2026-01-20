import Hodge.Analytic.Advanced.IntegrationTests
import Hodge.Analytic.Laplacian.ConnectionTests
import Hodge.Kahler.Lefschetz.LefschetzTests
import Hodge.GMT.GMTTests
import Hodge.Classical.CycleClass

/-!
# Master Tests (Round 6)

This file is a small “integration test harness” that imports all per-agent test files and
adds a few cross-module typechecking checks.

It is intended for **build verification**, not for the main proof track.
-/

noncomputable section

open Classical Hodge
open scoped Manifold

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X] [Nonempty X]

/-! ## Cross-module smoke tests -/

-- CycleClass: PD form is closed, hence yields a cohomology class.
example (p : ℕ) (Z : Set X) :
    IsFormClosed (CycleClass.poincareDualForm n X p Z) :=
  CycleClass.poincareDualForm_isClosed n X p Z

example (p : ℕ) (Z : Set X) :
    DeRhamCohomologyClass n X (2 * p) :=
  Hodge.ofForm (CycleClass.poincareDualForm n X p Z) (CycleClass.poincareDualForm_isClosed n X p Z)
