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

/-- **Harmonic characterization (stub)**.

In full Hodge theory one proves `Δω = 0 ↔ (dω = 0 ∧ δω = 0)` using the L² inner product.

In our current architecture, `⋆ = 0`, hence `δ = 0`, hence the Laplacian definition
`Δ = dδ + δd` is identically zero; consequently both “summands” vanish for all ω. This lemma
records the resulting *formal* characterization that is stable under future upgrades. -/
theorem isHarmonic_iff_closed_and_coclosed {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n)
    (ω : SmoothForm n X k) :
    IsHarmonic (n := n) (X := X) (k := k) hk hk' ω ↔
      (smoothExtDeriv (Codifferential.codifferential (n := n) (X := X) (k := k) ω) = 0 ∧
        Codifferential.codifferential (n := n) (X := X) (k := k + 1) (smoothExtDeriv ω) = 0) := by
  -- Both conjuncts are trivial since `δ = 0`.
  simp [IsHarmonic, HodgeLaplacian.laplacian_construct]

end HarmonicForms
end Hodge
