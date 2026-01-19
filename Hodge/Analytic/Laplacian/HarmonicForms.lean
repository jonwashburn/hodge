import Hodge.Analytic.Laplacian.HodgeLaplacian

/-!
# Harmonic forms (skeleton / off proof track)

This file introduces a lightweight interface for *harmonic forms*:

- A `k`-form `ω` is harmonic if `Δω = 0`.

With the current placeholder Laplacian (zero operator), every form is harmonic. This is **not**
mathematically meaningful, but it provides a stable API that can be upgraded once the Hodge star
and codifferential are implemented nontrivially.

This module is **off proof track** unless explicitly imported.
-/

noncomputable section

open Classical

namespace Hodge
namespace HarmonicForms

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-- A form is harmonic if its Laplacian vanishes. -/
def IsHarmonic {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n) (ω : SmoothForm n X k) : Prop :=
  HodgeLaplacian.laplacian_construct (n := n) (X := X) (k := k) hk hk' ω = 0

@[simp] theorem isHarmonic_iff {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n) (ω : SmoothForm n X k) :
    IsHarmonic (n := n) (X := X) (k := k) hk hk' ω ↔ True := by
  -- With the placeholder Laplacian, `Δω = 0` is always true.
  simp [IsHarmonic]

end HarmonicForms
end Hodge
