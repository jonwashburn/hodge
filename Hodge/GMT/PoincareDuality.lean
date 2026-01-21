import Hodge.Classical.CycleClass
import Hodge.GMT.CurrentToForm
import Hodge.GMT.IntegrationCurrent

/-!
# GMT: Poincaré Duality Interface (wrapper)

The current proof pipeline in this repository uses the “Poincaré dual form” interface
implemented in `Hodge.Classical.CycleClass`.

This file provides the module/name layout referenced by the operational plan, by
re-exporting the CycleClass constructors.
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

namespace Hodge.GMT

abbrev PoincareDualFormData := CycleClass.PoincareDualFormData

abbrev poincareDualFormExists := CycleClass.poincareDualFormExists
abbrev poincareDualForm := CycleClass.poincareDualForm

/-- Construct the Poincaré dual form via the `CycleClass` placeholder interface.

This is the *current* bridge used by the proof-track development. -/
abbrev poincareDualForm_construct_cycleClass := CycleClass.poincareDualForm

/-- Poincaré dual form constructed from the (integration current) → (regularization) pipeline.

This matches the operational plan sketch:
`regularizeCurrentToForm (integrationCurrent p Z)`.

At the moment both stages are placeholders, so this returns `0`. -/
noncomputable def poincareDualForm_construct_fromCurrent {n : ℕ} {X : Type*} {p : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X]
    (Z : Set X) : SmoothForm n X (2 * p) :=
  regularizeCurrentToForm (n := n) (X := X) (k := 2 * p)
    (integrationCurrent (n := n) (X := X) p Z)

/-- Construct the Poincaré dual form via the “current → regularize” pipeline.

This matches the operational plan naming (`poincareDualForm_construct`). -/
noncomputable abbrev poincareDualForm_construct := @poincareDualForm_construct_fromCurrent

/-! ## Connection to cohomology (documentation-level) -/

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]

/-- A cohomology class associated to a set `Z`, using the *current proof-track* PD-form interface.

This uses the `CycleClass.poincareDualForm` placeholder (which provides closedness), so it
produces a well-typed de Rham class.

**Gap (documented)**: relating this class to the “integration current → regularize” pipeline
requires real integration currents and a regularization theorem. -/
noncomputable def gmt_cycle_to_cohomology_path (p : ℕ) (Z : Set X) :
    DeRhamCohomologyClass n X (2 * p) :=
  Hodge.ofForm (CycleClass.poincareDualForm n X p Z) (CycleClass.poincareDualForm_isClosed n X p Z)

end Hodge.GMT
