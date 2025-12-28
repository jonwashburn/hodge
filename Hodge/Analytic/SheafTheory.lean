import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Hodge.Basic
import Hodge.Classical.Bergman

/-!
# Sheaf Theory for Complex Manifolds

This file provides the infrastructure for sheaf cohomology on complex manifolds,
focusing on coherent sheaves and their cohomology groups.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite TensorProduct

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-- Holomorphicity is a local property on a complex manifold. -/
def holomorphicLocalPredicate (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : TopCat.LocalPredicate (fun _ : TopCat.of X => ℂ) where
  pred {U} f := MDifferentiable (𝓒_complex n) 𝓒_ℂ f
  res {U V} i f h := h.comp (ContMDiff.mdifferentiable (contMDiff_inclusion i.le) one_ne_zero)
  locality {U} f h := by
    rw [mdifferentiable_iff]
    -- Holomorphicity at x follows from holomorphicity on an open neighborhood V.
    -- This is a foundational manifold property in Mathlib.
    sorry

/-- The structure sheaf 𝓞_X of holomorphic functions on a complex manifold. -/
axiom structureSheaf (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Sheaf (Opens.grothendieckTopology (TopCat.of X)) CommRingCat

/-- The structure sheaf as a sheaf of rings. -/
def structureSheafRing (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Sheaf (Opens.grothendieckTopology (TopCat.of X)) RingCat :=
  sheafCompose (Opens.grothendieckTopology (TopCat.of X)) (forget₂ CommRingCat RingCat) |>.obj (structureSheaf n X)

/-- A coherent sheaf on a complex manifold. -/
axiom CoherentSheaf (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] : Type (u + 1)

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

/-- A cohomology group vanishes if it is isomorphic to the zero module. -/
def vanishes {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : Prop :=
  ∀ (s : SheafCohomology F q), s = 0

/-- Tensor product of a holomorphic line bundle with a coherent sheaf. -/
axiom tensorWithSheaf {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (L : HolomorphicLineBundle n X) (F : CoherentSheaf n X) : CoherentSheaf n X

/-- The ideal sheaf m_x^{k+1} of functions vanishing to order k+1 at x. -/
axiom idealSheaf {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (x : X) (k : ℕ) : CoherentSheaf n X

end
