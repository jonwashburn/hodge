/-
Copyright (c) 2026 Hodge Formalization Project. All rights reserved.
Released under Apache 2.0 license.
Authors: Deep Track Formalization
-/
import Hodge.Classical.CycleClass
import Hodge.Classical.GAGA
import Hodge.Classical.PoincareDualityFromCurrents

/-!
# Deep Pillar: Poincaré duality / fundamental class / spine bridge (stub-free)

This module is the semantic landing pad for the “PD/GMT bridge” pillar in the playbook.

**Important (no gotchas)**: this file intentionally does **not** assert deep facts by fake proofs
(`= 0`, `True`, or `rfl`). Instead, the proof spine already has explicit interfaces for the
missing theorems:

- `CycleClass.PoincareDualityFromCurrentsData` (PD via integration currents);
- `SpineBridgeData_data` (comparison of the geometric fundamental class with the spine’s representing form).

To make the development mathematically unconditional, the next real work here is:

1. Construct integration currents for algebraic/analytic sets from real GMT (`OrientedRectifiableSetData`);
2. Prove representability / de Rham comparison needed to produce a *form* representing that current;
3. Prove the TeX spine comparison theorem (Harvey–Lawson + GAGA output has class `[γ]`).
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

namespace Hodge.Deep.PoincareDuality

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-!
## Re-exports (interfaces)

The two core interfaces that must eventually be discharged by real proofs:
-/

abbrev PoincareDualityFromCurrents (p : ℕ)
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)] :=
  CycleClass.PoincareDualityFromCurrentsData n X p

abbrev SpineBridge (p : ℕ)
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    [SignedAlgebraicCycleSupportData n X p] :=
  SpineBridgeData_data n X p

/-!
## Re-export (current proof-spine bridge hook)

This is the exact bridge lemma the proof spine needs on the **data‑first** pipeline.
It is *not* proved here; it is assumed via the `SpineBridgeData_data` interface.
-/

theorem cycleClass_geom_eq_representingForm_data {p : ℕ}
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    [SignedAlgebraicCycleSupportData n X p]
    [SpineBridgeData_data n X p]
    (Z : SignedAlgebraicCycle n X p) :
    Z.cycleClass_geom_data = ofForm Z.representingForm Z.representingForm_closed :=
  SpineBridgeData_data.fundamental_eq_representing (n := n) (X := X) (p := p) (Z := Z)

end Hodge.Deep.PoincareDuality

end
