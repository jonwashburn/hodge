import Hodge.Analytic.IntegralCurrents

/-!
# GMT: Integral Current Space (wrapper)

Integral currents are defined in `Hodge.Analytic.IntegralCurrents`.  This file provides
some lightweight “space of integral currents with bounded mass” definitions under the
`Hodge.GMT` module hierarchy referenced in the operational plan.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

/-- Boundary mass of an integral current.

For `k = 0`, we define this as `0` (there is no boundary in negative degree).
For `k = k' + 1`, this is the mass of the boundary current. -/
def bdryMass {n : ℕ} {X : Type*} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (T : IntegralCurrent n X k) : ℝ := by
  cases k with
  | zero =>
    exact 0
  | succ k' =>
    exact Current.mass (Current.boundary (k := k') T.toFun)

/-- Integral currents whose mass and boundary mass are bounded by `M`. -/
def BoundedIntegralCurrents {n : ℕ} {X : Type*} (k : ℕ) (M : ℝ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] :
    Set (IntegralCurrent n X k) :=
  { T | Current.mass T.toFun ≤ M ∧ bdryMass (n := n) (X := X) (k := k) T ≤ M }

end Hodge.GMT
