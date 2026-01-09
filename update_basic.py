import sys

content = """import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Defs.Induced
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Analysis.Analytic.Basic

noncomputable section

open Classical TopologicalSpace
open scoped Manifold

set_option autoImplicit false

universe u

/-- We work with the model tangent space `E = ℂⁿ` (Mathlib's `EuclideanSpace ℂ (Fin n)`).

In Mathlib, `TangentSpace (𝓒_complex n) x` is a type synonym for this `E`, so this is the
correct (and non-dependent) fiber to use for continuity of sections. -/
abbrev TangentModel (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The (fiberwise) space of continuous alternating `k`-linear maps on the model tangent space.
This is the correct object to put a norm/topology on (Mathlib: operator norm on
`ContinuousAlternatingMap`). -/
abbrev FiberAlt (n : ℕ) (k : ℕ) := (TangentModel n) [⋀^Fin k]→L[ℂ] ℂ

def 𝓒_complex (n : ℕ) : ModelWithCorners ℂ (EuclideanSpace ℂ (Fin n)) (EuclideanSpace ℂ (Fin n)) :=
  modelWithCornersSelf ℂ (EuclideanSpace ℂ (Fin n))

/-- **Analytic Sets** (Rigorous Definition).
    A subset S ⊆ X is analytic if it is locally the zero locus of a finite
    collection of holomorphic functions. -/
def IsAnalyticSet {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] (S : Set X) : Prop :=
  IsClosed S ∧ ∀ x ∈ X, ∃ U ∈ 𝓝 x, ∃ (fs : Finset (X → ℂ)),
    (∀ f ∈ fs, MDifferentiable (𝓒_complex n) 𝓘(ℂ, ℂ) f) ∧
    S ∩ U = { y ∈ U | ∀ f ∈ fs, f y = 0 }

/-- **Projective Complex Manifold** (Rigorous Definition).
    A projective complex manifold is a compact complex manifold that carries
    an algebraic structure (as a scheme) such that its analytic and algebraic
    properties are equivalent (Serre's GAGA). -/
class ProjectiveComplexManifold (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    extends IsManifold (𝓒_complex n) ⊤ X, CompactSpace X where
  embedding_dim : ℕ
  /-- The underlying algebraic scheme structure. -/
  algebraic_scheme : AlgebraicGeometry.Scheme
  /-- The homeomorphism between the scheme's carrier and the manifold. -/
  algebraic_to_analytic : algebraic_scheme.carrier ≃ₜ X
  /-- **GAGA Equivalence**: A subset is analytic iff it is Zariski-closed in the scheme. -/
  gaga : ∀ (S : Set X), IsAnalyticSet S ↔ IsClosed (algebraic_to_analytic.symm '' S)

/-- **Algebraic Sets** (Rigorous Definition).
    A subset Z ⊆ X is algebraic if it is closed in the Zariski topology of the
    underlying scheme. -/
def IsAlgebraicSet (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [P : ProjectiveComplexManifold n X] (Z : Set X) : Prop :=
  IsClosed (P.algebraic_to_analytic.symm '' Z)

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
"""

with open('Hodge/Basic.lean', 'w') as f:
    f.write(content)
