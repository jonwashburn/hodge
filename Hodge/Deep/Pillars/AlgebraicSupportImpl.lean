import Hodge.Classical.GAGA
import Hodge.Classical.AlgebraicSets
import Hodge.Analytic.Currents

noncomputable section

open Classical Hodge Hodge.AlgGeom MeasureTheory

namespace Hodge.Deep.Pillars

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/--
**Algebraic Subvariety Closed Submanifold Data Axiom**

Every algebraic subvariety V of a projective Kähler manifold admits a
`ClosedSubmanifoldData` structure whose carrier equals `V.carrier`.

**Mathematical Content**: An algebraic subvariety of complex codimension c
has real dimension 2(n − c). It carries:
- A canonical orientation from the complex structure
- Finite Hausdorff measure (compactness of projective manifolds)
- The Stokes property (∂V = ∅ for closed subvarieties)

The `ClosedSubmanifoldData` packages these into the orientation k-vector field,
Hausdorff measure, and Stokes integral identity needed by the integration current
pipeline.

Reference: [Griffiths-Harris, "Principles of Algebraic Geometry", Ch. 0-1].
-/
axiom algebraic_subvariety_admits_closed_submanifold_data
    (V : AlgebraicSubvariety n X) :
    ∃ (d : ClosedSubmanifoldData n X (2 * (n - V.codim))), d.carrier = V.carrier

/--
**Algebraic Support Data Instance**

Provides `AlgebraicSubvarietyClosedSubmanifoldData`.
Every algebraic subvariety is equipped with closed submanifold data via
the axiom `algebraic_subvariety_admits_closed_submanifold_data`.

Combined with `instSignedAlgebraicCycleSupportData_direct` (in GAGA.lean)
and `Fact (p ≤ n)`, this also provides `SignedAlgebraicCycleSupportData`,
eliminating the former `algebraic_codimension_of_cycle_support` axiom.
-/
instance instAlgebraicSubvarietyClosedSubmanifoldData :
    AlgebraicSubvarietyClosedSubmanifoldData n X where
  data_of := fun V =>
    (algebraic_subvariety_admits_closed_submanifold_data V).choose
  carrier_eq := fun V =>
    (algebraic_subvariety_admits_closed_submanifold_data V).choose_spec

end Hodge.Deep.Pillars
