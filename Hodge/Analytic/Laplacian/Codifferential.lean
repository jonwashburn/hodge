import Hodge.Analytic.Norms
import Hodge.Analytic.Forms

noncomputable section

open Classical Hodge

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-! ## Codifferential (formal adjoint of d) -/

/-- Linear-map version of the Hodge star on k-forms. -/
noncomputable def hodgeStarLinear (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (n - k) where
  toFun := hodgeStar (n := n) (X := X) (k := k)
  map_add' := by
    intro α β
    simpa using (hodgeStar_add (n := n) (X := X) (k := k) α β)
  map_smul' := by
    intro c α
    simpa using (hodgeStar_smul (n := n) (X := X) (k := k) c α)

/-- Codifferential `δ = (-1)^{nk+n+1} ⋆ d ⋆` as a linear map on k-forms.

The target degree is the literal output of `⋆ d ⋆`, i.e. `n - (n - k + 1)`;
when `k ≤ n` this simplifies to `k - 1`. -/
noncomputable def codifferential (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (n - (n - k + 1)) := by
  classical
  let star_k : SmoothForm n X k →ₗ[ℂ] SmoothForm n X (n - k) :=
    hodgeStarLinear (n := n) (X := X) (k := k)
  let d_nk : SmoothForm n X (n - k) →ₗ[ℂ] SmoothForm n X (n - k + 1) :=
    extDerivLinearMap n X (n - k)
  let star_nk1 : SmoothForm n X (n - k + 1) →ₗ[ℂ] SmoothForm n X (n - (n - k + 1)) :=
    hodgeStarLinear (n := n) (X := X) (k := n - k + 1)
  exact (codifferentialSign n k : ℂ) • (star_nk1.comp (d_nk.comp star_k))

@[simp] theorem codifferential_zero (k : ℕ) :
    codifferential (n := n) (X := X) (k := k) 0 = 0 := by
  simpa using (codifferential (n := n) (X := X) (k := k)).map_zero

@[simp] theorem codifferential_add {k : ℕ} (α β : SmoothForm n X k) :
    codifferential (n := n) (X := X) (k := k) (α + β) =
      codifferential (n := n) (X := X) (k := k) α +
      codifferential (n := n) (X := X) (k := k) β := by
  simpa using (codifferential (n := n) (X := X) (k := k)).map_add α β

@[simp] theorem codifferential_smul {k : ℕ} (c : ℂ) (α : SmoothForm n X k) :
    codifferential (n := n) (X := X) (k := k) (c • α) =
      c • codifferential (n := n) (X := X) (k := k) α := by
  simpa using (codifferential (n := n) (X := X) (k := k)).map_smul c α

end
