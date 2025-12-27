import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Hodge.Basic
import Hodge.Classical.Bergman

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-- The local predicate of being holomorphic. -/
def holomorphicLocalPredicate (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : TopCat.LocalPredicate (fun _ : X => ℂ) where
  pred {U} f := MDifferentiable (𝓒_complex n) 𝓒_ℂ f
  res {U V} i f h := h.comp (Opens.isOpenEmbedding_of_le i.le).mdifferentiable
  locality {U} f h := by
    rw [mdifferentiable_iff]
    intro x
    specialize h x
    obtain ⟨V, hxV, i, hV⟩ := h
    have h_diff := mdifferentiable_iff.mp hV ⟨x.1, hxV⟩
    exact (Opens.isOpenEmbedding_of_le i.le).mdifferentiableAt_iff.mp h_diff

/-- The ring of holomorphic functions on an open set U. -/
def HolomorphicFunctions (U : Opens X) : Type u :=
  { f : U → ℂ // MDifferentiable (𝓒_complex n) 𝓒_ℂ f }

instance (U : Opens X) : CommRing (HolomorphicFunctions U) := 
  Subring.toCommRing (Subring.mk'
    { f : U → ℂ | MDifferentiable (𝓒_complex n) 𝓒_ℂ f }
    (mdifferentiable_const _)
    (fun _ _ h1 h2 => MDifferentiable.mul h1 h2)
    (fun _ h => MDifferentiable.neg h)
    (fun _ _ h1 h2 => MDifferentiable.add h1 h2))

/-- The structure sheaf 𝓞_X of holomorphic functions on a complex manifold. -/
def structureSheaf (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Sheaf CommRingCat X where
  val := {
    obj := fun U => CommRingCat.of (HolomorphicFunctions U.unop)
    map := fun {U V} i f => ⟨f.1 ∘ i.unop, (holomorphicLocalPredicate n X).res i.unop f.1 f.2⟩
    map_id := fun U => by ext; rfl
    map_comp := fun {U V W} i j => by ext; rfl
  }
  cond := by
    apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommRingCat) _).mpr
    exact TopCat.subpresheafToTypes.isSheaf (holomorphicLocalPredicate n X)

/-- The site of open sets on X. -/
def holomorphicSite (X : Type u) [TopologicalSpace X] : GrothendieckTopology (Opens X) :=
  Opens.site X

/-- The structure sheaf as a sheaf of rings. -/
def structureSheafRing (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Sheaf (holomorphicSite X) RingCat :=
  sheafCompose (holomorphicSite X) (forget₂ CommRingCat RingCat) |>.obj (structureSheaf n X)

/-- The category of sheaves of modules over the structure sheaf. -/
def SheafOfOMonodules (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] :=
  SheafOfModules (structureSheafRing n X)

EOF
