import Hodge.Analytic.Laplacian
import Hodge.Analytic.HodgeLaplacian

/-!
# Laplacian Connection Tests (Round 3 / Agent 3)

This file is a lightweight “wiring test” that the Hodge-star → codifferential → Laplacian →
harmonic-form interfaces compose without type errors.

It is **not** intended to be mathematically deep; most operators are still semantic stubs
(notably `⋆ = 0`, hence `δ = 0`), but the definitions are arranged in the correct shapes so the
real proofs can be dropped in later with minimal churn.
-/

noncomputable section

open Classical

namespace Hodge
namespace Analytic
namespace LaplacianConnectionTests

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-! ## δ² = 0 -/

theorem test_codifferential_squared_zero {k : ℕ} (ω : SmoothForm n X k) :
    Codifferential.codifferential (n := n) (X := X) (k := (2 * n - (2 * n - k + 1)))
        (Codifferential.codifferential (n := n) (X := X) (k := k) ω) = 0 := by
  simpa using (Codifferential.codifferential_squared_zero (n := n) (X := X) (k := k) ω)

/-! ## Δ = dδ + δd -/

theorem test_hodgeLaplacian_formula {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n) (ω : SmoothForm n X k) :
    HodgeLaplacian.hodgeLaplacian_construct (n := n) (X := X) (k := k) hk hk' ω =
      castForm (by omega)
          (smoothExtDeriv (Codifferential.codifferential (n := n) (X := X) (k := k) ω)) +
        castForm (by omega)
          (Codifferential.codifferential (n := n) (X := X) (k := k + 1) (smoothExtDeriv ω)) := by
  rfl

/-! ## Harmonic characterization (stub) -/

theorem test_isHarmonic_iff_closed_and_coclosed {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n)
    (ω : SmoothForm n X k) :
    HarmonicForms.IsHarmonic (n := n) (X := X) (k := k) hk hk' ω ↔
      (smoothExtDeriv (Codifferential.codifferential (n := n) (X := X) (k := k) ω) = 0 ∧
        Codifferential.codifferential (n := n) (X := X) (k := k + 1) (smoothExtDeriv ω) = 0) := by
  simpa using
    (HarmonicForms.isHarmonic_iff_closed_and_coclosed (n := n) (X := X) (k := k) hk hk' ω)

/-! ## Connection to the L²-oriented `Hodge/Analytic/HodgeLaplacian.lean` -/

theorem test_laplacian_connects_to_HodgeLaplacian {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n)
    (ω : SmoothForm n X k) :
    True := by
  -- This is a “wiring check”: both notions of Laplacian exist and typecheck in the same context.
  let _ : SmoothForm n X k :=
    HodgeLaplacian.hodgeLaplacian_construct (n := n) (X := X) (k := k) hk hk' ω
  let _ : SmoothForm n X k :=
    hodgeLaplacian (n := n) (X := X) (k := k) hk hk' ω
  trivial

end LaplacianConnectionTests
end Analytic
end Hodge
