import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Hodge.Basic

/-!
# Sheaf Theory for Complex Manifolds

This file provides axiomatized definitions for sheaf-theoretic constructions
needed in the Hodge conjecture formalization.

## Main Definitions

- `CoherentSheaf`: A coherent sheaf on a complex projective manifold
- `SheafCohomology`: The q-th sheaf cohomology group H^q(X, F)
- `vanishes`: Predicate for vanishing cohomology groups
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-- The structure sheaf 𝓞_X of holomorphic functions on a complex manifold. -/
axiom structureSheaf (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Sheaf (Opens.grothendieckTopology (TopCat.of X)) CommRingCat

/-- A coherent sheaf on a complex manifold. -/
axiom CoherentSheaf (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] : Type u

/-- The q-th sheaf cohomology group H^q(X, F). -/
axiom SheafCohomology {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : Type u

axiom SheafCohomology.instAddCommGroup {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : AddCommGroup (SheafCohomology F q)
attribute [instance] SheafCohomology.instAddCommGroup

axiom SheafCohomology.instModule {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : Module ℂ (SheafCohomology F q)
attribute [instance] SheafCohomology.instModule

/-- A cohomology group vanishes if all elements are zero. -/
def vanishes {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : Prop :=
  ∀ (s : SheafCohomology F q), s = 0

end
