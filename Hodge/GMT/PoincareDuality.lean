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

/-- Construct the Poincaré dual form (currently via the CycleClass placeholder). -/
abbrev poincareDualForm_construct := CycleClass.poincareDualForm

/-- Poincaré dual form constructed from the (integration current) → (regularization) pipeline.

This matches the operational plan sketch:
`regularizeCurrentToForm (integrationCurrent p Z)`.

At the moment both stages are placeholders, so this returns `0`. -/
noncomputable def poincareDualForm_construct_fromCurrent {n : ℕ} {X : Type*} {p : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    (Z : Set X) : SmoothForm n X (2 * p) :=
  regularizeCurrentToForm (n := n) (X := X) (k := 2 * p)
    (integrationCurrent (n := n) (X := X) p Z)

end Hodge.GMT
