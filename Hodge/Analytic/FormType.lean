import Hodge.Basic

noncomputable section

open Classical Module Manifold
open scoped Pointwise Manifold

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-- A section of differential forms is “smooth” (for this development) if the alternating map
varies smoothly in `x`, as a map into the normed space of continuous alternating maps.

This matches the manuscript-level argument: smooth coefficients give differentiability of the section
in the manifold sense. -/
def IsSmoothAlternating (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (k : ℕ) (f : X → FiberAlt n k) : Prop :=
  ContMDiff (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ⊤ f

@[ext]
structure SmoothForm (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  as_alternating : X → FiberAlt n k
  is_smooth : IsSmoothAlternating n X k as_alternating

end
