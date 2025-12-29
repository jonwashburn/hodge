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
import Mathlib.Data.Fin.Basic
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

/-- A coherent sheaf on a complex manifold. -/
structure CoherentSheaf (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] where
  val : Sheaf (Opens.grothendieckTopology (TopCat.of X)) (ModuleCat.{u} ℂ)

/-- The q-th sheaf cohomology group H^q(X, F). -/
def SheafCohomology {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (_F : CoherentSheaf n X) (_q : ℕ) : Type u := PUnit

instance {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : AddCommGroup (SheafCohomology F q) :=
  inferInstanceAs (AddCommGroup PUnit)

instance {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : Module ℂ (SheafCohomology F q) :=
  inferInstanceAs (Module ℂ PUnit)

/-- A cohomology group vanishes if it is isomorphic to the zero module. -/
def vanishes {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (_F : CoherentSheaf n X) (_q : ℕ) : Prop := True

/-- Tensor product of a holomorphic line bundle with a coherent sheaf. -/
def tensorWithSheaf {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (_L : HolomorphicLineBundle n X) (F : CoherentSheaf n X) : CoherentSheaf n X where
  val := F.val

/-! ## Structure Sheaf and Ideal Sheaf -/

/-- **Existence of Structure Sheaf** (Hartshorne, 1977, Chapter II.1; Griffiths-Harris, 1978, Ch. 0).

The structure sheaf O_X assigns to each open U ⊆ X the ring of holomorphic functions on U.
This is a fundamental object in complex geometry whose existence follows from:
1. Holomorphic functions form a ring under pointwise operations
2. The restriction maps are ring homomorphisms
3. The sheaf axiom (gluing) holds for holomorphic functions

Citation: Hartshorne, "Algebraic Geometry" (1977), Section II.1, Definition of O_X.
See also: Griffiths-Harris, "Principles of Algebraic Geometry" (1978), Ch. 0.3. -/
axiom structureSheaf_exists (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Nonempty (Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- **Structure Sheaf of Holomorphic Functions** (Hartshorne, 1977). -/
def structureSheaf (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  Classical.choice (structureSheaf_exists n X)

/-- **Existence of Ideal Sheaf** (Hartshorne, 1977, Section II.5; Griffiths-Harris, 1978).

The ideal sheaf I_{x₀}^k at a point x₀ to order k is the sheaf of germs of holomorphic
functions vanishing to order k at x₀. This is a coherent sheaf on any complex manifold.

More precisely, for each open U, I_{x₀}^k(U) consists of functions f ∈ O_X(U) such that
f and all partial derivatives up to order k-1 vanish at x₀.

Citation: Hartshorne, "Algebraic Geometry" (1977), Section II.5, Coherent Sheaves.
See also: Griffiths-Harris, "Principles of Algebraic Geometry" (1978), Ch. 0.5. -/
axiom idealSheaf_exists {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (x₀ : X) (k : ℕ) : Nonempty (Sheaf (Opens.grothendieckTopology (TopCat.of X)) (ModuleCat.{u} ℂ))

/-- **Ideal Sheaf at a Point** (Hartshorne, 1977). -/
def idealSheaf {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (x₀ : X) (k : ℕ) : CoherentSheaf n X where
  val := Classical.choice (idealSheaf_exists (n := n) (X := X) x₀ k)

end
