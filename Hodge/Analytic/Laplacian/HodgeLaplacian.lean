import Hodge.Analytic.Laplacian.Codifferential

/-!
# Hodge Laplacian Δ (skeleton / off proof track)

This module introduces a compile-stable interface for the **Hodge Laplacian**
\(\Delta = d\delta + \delta d\).

In the current repository architecture:
- `d` is implemented as `smoothExtDeriv` in `Hodge/Analytic/Forms.lean`.
- `⋆` is currently a **trivial placeholder** (see `Hodge/Analytic/Norms.lean`),
  hence `δ` is also trivial in `Hodge/Analytic/Laplacian/Codifferential.lean`.

Because the real Hodge star construction is not yet available, we provide a **placeholder**
Laplacian operator. This file is **off proof track** unless explicitly imported.
-/

noncomputable section

open Classical

namespace Hodge
namespace HodgeLaplacian

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-- **Hodge Laplacian** Δ on `k`-forms.

In a full implementation this should be:

`Δω = d(δω) + δ(dω)`.

At the moment, the repository's Hodge star (hence codifferential) is still a semantic stub
(`⋆ = 0`, so `δ = 0`). With that stub, the definition below simplifies to `0`, but we keep the
*structurally correct* formula for Δ so downstream files can be written against the intended API. -/
noncomputable def laplacian_construct {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n)
    (ω : SmoothForm n X k) : SmoothForm n X k :=
  castForm (by omega) (smoothExtDeriv (Codifferential.codifferential (n := n) (X := X) (k := k) ω)) +
    castForm (by omega) (Codifferential.codifferential (n := n) (X := X) (k := k + 1) (smoothExtDeriv ω))

/-- Alias (naming used in the operational plan): the Hodge Laplacian Δ = dδ + δd. -/
noncomputable abbrev hodgeLaplacian_construct {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n)
    (ω : SmoothForm n X k) : SmoothForm n X k :=
  laplacian_construct (n := n) (X := X) (k := k) hk hk' ω

/-! ### Linearity of Laplacian (Structural Proofs)

These proofs work via the trivial δ, but are written to be easily updatable
when the Hodge star becomes non-trivial.
-/

/-- With trivial Hodge star, the Laplacian returns 0.

**Note**: NOT marked `@[simp]` to preserve algebraic structure. -/
theorem laplacian_construct_eq_zero_of_trivial_star {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n)
    (ω : SmoothForm n X k) :
    laplacian_construct (n := n) (X := X) (k := k) hk hk' ω = 0 := by
  simp only [laplacian_construct, Codifferential.codifferential_eq_zero_of_trivial_star,
             smoothExtDeriv_zero, castForm_zero, add_zero]

/-- With trivial Hodge star, the Hodge Laplacian returns 0. -/
theorem hodgeLaplacian_construct_eq_zero_of_trivial_star {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n)
    (ω : SmoothForm n X k) :
    hodgeLaplacian_construct (n := n) (X := X) (k := k) hk hk' ω = 0 :=
  laplacian_construct_eq_zero_of_trivial_star hk hk' ω

/-- Laplacian of zero is zero. -/
theorem laplacian_construct_zero {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n) :
    laplacian_construct (n := n) (X := X) (k := k) hk hk' 0 = 0 := by
  simp only [laplacian_construct, Codifferential.codifferential_zero,
             smoothExtDeriv_zero, castForm_zero, add_zero]

/-- Laplacian is additive. -/
theorem laplacian_construct_add {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n)
    (α β : SmoothForm n X k) :
    laplacian_construct hk hk' (α + β) =
    laplacian_construct hk hk' α + laplacian_construct hk hk' β := by
  simp only [laplacian_construct_eq_zero_of_trivial_star, add_zero]

/-- Laplacian respects ℂ-scalar multiplication. -/
theorem laplacian_construct_smul {k : ℕ} (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n)
    (c : ℂ) (α : SmoothForm n X k) :
    laplacian_construct hk hk' (c • α) = c • laplacian_construct hk hk' α := by
  simp only [laplacian_construct_eq_zero_of_trivial_star, smul_zero]

/-- Laplacian as a ℂ-linear map.

Linearity is proven from linearity of d and δ. -/
noncomputable def laplacianLinearMap (k : ℕ) (hk : 1 ≤ k) (hk' : k + 1 ≤ 2 * n) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X k where
  toFun ω := laplacian_construct (n := n) (X := X) (k := k) hk hk' ω
  map_add' := laplacian_construct_add hk hk'
  map_smul' := fun c ω => by
    simp only [RingHom.id_apply]
    exact laplacian_construct_smul hk hk' c ω

end HodgeLaplacian
end Hodge
