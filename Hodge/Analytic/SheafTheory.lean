import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Hodge.Basic
import Hodge.Classical.Bergman

noncomputable section

open CategoryTheory TopologicalSpace

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-- The presheaf of holomorphic functions on X. -/
def holomorphicFunctionsPresheaf (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Presheaf CommRingCat X where
  obj U := CommRingCat.of (MDifferentiable (𝓒_complex n) 𝓒_ℂ (fun x : U.unop => (x.1 : X)))
  map f := sorry -- Restriction map
  map_id := sorry
  map_comp := sorry

/-- The structure sheaf 𝓞_X of holomorphic functions on a complex manifold. -/
def structureSheaf (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Sheaf CommRingCat X :=
  sorry

