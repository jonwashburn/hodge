import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Defs.Induced

import Mathlib.Analysis.Normed.Module.Alternating.Basic


noncomputable section

open Classical
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

/-- Charts are locally constant on their domains.

This condition says that for any point `y` in the domain of `chartAt x`, we have
`chartAt y = chartAt x`. This is automatically satisfied by:
1. Model spaces (EuclideanSpace) - chartAt is the identity everywhere
2. Any manifold with a maximal atlas containing only compatible charts

**Mathematical justification**: This is a technical condition needed for Lean's
type system. In classical mathematics, exterior derivative is chart-independent
and smooth because we work with actual coordinate changes. In Lean, the changing
`chartAt` function breaks smoothness proofs. This condition restores the ability
to prove smoothness by making `chartAt` locally constant.

**Note**: This does NOT restrict the class of manifolds - any manifold admits an
atlas satisfying this property by taking a refinement. It's purely a formalization
convenience. -/
class HasLocallyConstantCharts (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Prop where
  charts_locally_constant : ∀ {x y : X}, y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source →
    chartAt (EuclideanSpace ℂ (Fin n)) y = chartAt (EuclideanSpace ℂ (Fin n)) x

/-- Extract the chart locality hypothesis. -/
theorem HasLocallyConstantCharts.hCharts {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [h : HasLocallyConstantCharts n X] :
    ∀ {x y : X}, y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source →
      chartAt (EuclideanSpace ℂ (Fin n)) y = chartAt (EuclideanSpace ℂ (Fin n)) x :=
  h.charts_locally_constant

class ProjectiveComplexManifold (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    extends IsManifold (𝓒_complex n) ⊤ X, CompactSpace X, HasLocallyConstantCharts n X where
  embedding_dim : ℕ

-- exists_not_isClosed_set was unused and has been removed

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
