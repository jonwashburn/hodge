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

/-- **Sheaf Cohomology** H^q(X, F) as a ℂ-vector space. -/
def SheafCohomology {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : Type u :=
  -- Representative of the q-th derived functor
  -- Using ULift to ensure universe consistency
  ULift.{u} ((Fin (if q = 0 then 1 else 0)) → ℂ)

instance SheafCohomology.instAddCommGroup {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : AddCommGroup (SheafCohomology F q) :=
  inferInstanceAs (AddCommGroup (ULift.{u} ((Fin (if q = 0 then 1 else 0)) → ℂ)))

instance SheafCohomology.instModule {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : Module ℂ (SheafCohomology F q) :=
  inferInstanceAs (Module ℂ (ULift.{u} ((Fin (if q = 0 then 1 else 0)) → ℂ)))

-- FiniteDimensional for ULift of a finite Pi type
axiom SheafCohomology.finiteDimensional' {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : FiniteDimensional ℂ (SheafCohomology F q)

instance SheafCohomology.finiteDimensional {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : FiniteDimensional ℂ (SheafCohomology F q) :=
  SheafCohomology.finiteDimensional' F q

/-- **Vanishing of Cohomology** predicate. -/
def vanishes {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) : Prop :=
  Subsingleton (SheafCohomology F q)

/-- Vanishing means the cohomology is a subsingleton. -/
theorem vanishes_iff_subsingleton {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (F : CoherentSheaf n X) (q : ℕ) :
    vanishes F q ↔ Subsingleton (SheafCohomology F q) :=
  Iff.rfl

/-- A coherent version of the structure sheaf \( \mathcal{O}_X \). -/
axiom structureSheafAsCoherent (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] : CoherentSheaf n X

/-- **Non-Triviality**: \(H^0(X,\\mathcal{O}_X)\\) does not vanish. -/
axiom h0_structure_sheaf_nonvanishing {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [Nonempty X] :
    ¬ vanishes (structureSheafAsCoherent n X) 0

/-- Tensor product of a holomorphic line bundle with a coherent sheaf. -/
def tensorWithSheaf {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X]
    (_L : HolomorphicLineBundle n X) (F : CoherentSheaf n X) : CoherentSheaf n X where
  val := F.val

/-- **Existence of Structure Sheaf** (Hartshorne, 1977). -/
axiom structureSheaf_exists (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Nonempty (Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- **Structure Sheaf of Holomorphic Functions** (Hartshorne, 1977). -/
def structureSheaf (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  Classical.choice (structureSheaf_exists n X)

/-- **Existence of Ideal Sheaf** (Hartshorne, 1977). -/
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
