import Hodge.Analytic.Norms
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

def CalibratedGrassmannian (p : ℕ) (x : X) : Set (Submodule ℂ (TangentSpace (𝓒_complex n) x)) :=
  { V | Module.finrank ℂ V = p }

def simpleCalibratedForm (p : ℕ) (_x : X) (_V : Submodule ℂ (TangentSpace (𝓒_complex n) _x)) :
    SmoothForm n X (2 * p) :=
  { as_alternating := fun _ => 0 }

def simpleCalibratedForms (p : ℕ) (x : X) : Set (SmoothForm n X (2 * p)) :=
  { ξ | ∃ (V : Submodule ℂ (TangentSpace (𝓒_complex n) x)),
    Module.finrank ℂ V = p ∧ ξ = simpleCalibratedForm p x V }

def calibratedCone (p : ℕ) (_x : X) : Set (SmoothForm n X (2 * p)) :=
  Set.univ

theorem calibratedCone_is_closed (p : ℕ) (x : X) :
    IsClosed (calibratedCone (n := n) (X := X) p x) := by
  sorry

def distToCone (p : ℕ) (_α : SmoothForm n X (2 * p)) (_x : X) : ℝ := 0

def coneDefect (p : ℕ) (_α : SmoothForm n X (2 * p)) : ℝ := 0

theorem radial_minimization (x : X) (ξ : SmoothForm n X (2 * p)) (α : SmoothForm n X (2 * p)) :
    pointwiseNorm ξ x = 1 →
    ∃ lam_star : ℝ, lam_star = max 0 (pointwiseInner α ξ x) ∧
    ∀ l ≥ (0 : ℝ), (pointwiseNorm (α - lam_star • ξ) x)^2 ≤ (pointwiseNorm (α - l • ξ) x)^2 := by
  sorry

theorem dist_cone_sq_formula (p : ℕ) (α : SmoothForm n X (2 * p)) (x : X) :
    (distToCone p α x)^2 = (pointwiseNorm α x)^2 -
      (sSup { r | ∃ ξ ∈ simpleCalibratedForms p x, r = max 0 (pointwiseInner α ξ x) })^2 := by
  sorry

def coneToNetConstant : ℝ := (11 / 9 : ℝ)^2

end
