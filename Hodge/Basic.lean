import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Defs.Induced

noncomputable section

open Classical

set_option autoImplicit false

universe u

def 𝓒_complex (n : ℕ) : ModelWithCorners ℂ (EuclideanSpace ℂ (Fin n)) (EuclideanSpace ℂ (Fin n)) :=
  modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin n))

class ProjectiveComplexManifold (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    extends IsManifold (𝓒_complex n) ⊤ X, CompactSpace X where
  embedding_dim : ℕ

axiom exists_not_isClosed_set (X : Type*) [TopologicalSpace X] [Nonempty X] : ∃ S : Set X, ¬ IsClosed S

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]

/-- The tangent space at a point on a complex manifold modeled on `EuclideanSpace ℂ (Fin n)`
    is definitionally equal to `EuclideanSpace ℂ (Fin n)`, which is a `NormedAddCommGroup`.
    We use `inferInstanceAs` to transfer this instance. -/
instance instNormedAddCommGroupTangentSpace (x : X) : NormedAddCommGroup (TangentSpace (𝓒_complex n) x) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin n)))

/-- The tangent space at a point on a complex manifold modeled on `EuclideanSpace ℂ (Fin n)`
    is definitionally equal to `EuclideanSpace ℂ (Fin n)`, which is a `NormedSpace ℂ`.
    We use `inferInstanceAs` to transfer this instance. -/
instance instNormedSpaceTangentSpace (x : X) : NormedSpace ℂ (TangentSpace (𝓒_complex n) x) :=
  inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin n)))

end
