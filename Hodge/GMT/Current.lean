import Hodge.Analytic.Currents

/-!
# GMT: Currents (wrapper)

The core current infrastructure in this repository lives in `Hodge.Analytic.Currents`
and is named `Current n X k`.

The operational plan (Agent 5) uses the name `DeRhamCurrent`; we provide it here as a
compatibility alias to `Current`.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

/-- Compatibility alias for the project’s core current type. -/
abbrev DeRhamCurrent (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] : Type _ :=
  Current n X k

/-- Boundary operator on currents, phrased using `Nat.sub` on degrees.

For `k = 0`, the boundary is defined to be `0` (since `k - 1 = 0` in `Nat`).
For `k = k' + 1`, this is `Current.boundary`. -/
def DeRhamCurrent.boundary {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    {k : ℕ} (T : DeRhamCurrent n X k) : DeRhamCurrent n X (k - 1) := by
  cases k with
  | zero =>
    -- Nat.sub: 0 - 1 = 0
    exact (0 : DeRhamCurrent n X 0)
  | succ k' =>
    -- Nat.sub: (k'+1) - 1 = k'
    simpa [DeRhamCurrent, Nat.succ_sub_one] using (Current.boundary (k := k') T)

end Hodge.GMT
