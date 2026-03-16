/-
Copyright (c) 2026 Hodge Formalization Project. All rights reserved.
Released under Apache 2.0 license.
Authors: TeX Spine Semantic Closure Implementation
-/
import Hodge.Classical.GAGA
import Hodge.Kahler.Main
import Hodge.Classical.PoincareDualityFromCurrents

/-!
# Geometric Cycle Class (TeX Spine Step 6)

This file provides the **geometric** definition of `cycleClass`, where the cohomology class
is computed from the **support** of the algebraic cycle (via fundamental class / Poincaré duality).

## Mathematical Content

Currently, `SignedAlgebraicCycle.cycleClass` is defined by:
```
cycleClass := ofForm representingForm representingForm_closed
```

This is a "proof-track-safe shortcut" that makes the cohomology relationship trivial.

The **geometric** definition on the proof track is data‑first:
```
cycleClass_geom_data := ofForm (FundamentalClassSet_data support_data) ...
```

And the **bridge theorem** (TeX spine culmination) proves:
```
cycleClass_geom_data(Z_from_spine(γ)) = ofForm γ
```

## Main Definitions

* `cycleClass_geom_data` - Geometric cycle class from explicit support data
* `spine_bridge_data` / `spine_bridge_data_with_data` - Data‑first bridge for spine‑produced cycles

## TeX Reference

This is the final step: geometric `cycleClass` + bridge theorem.

## Status

⚠️ PARALLEL TRACK - Interface for future implementation. Build with:
```bash
lake build Hodge.Classical.GeometricCycleClass
```
-/

noncomputable section

open Classical TopologicalSpace Hodge
open SignedAlgebraicCycle (cycleClass_geom_data)

set_option autoImplicit false

namespace Hodge.TexSpine.GeometricCycleClass

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-! ## Data‑First (Preferred) -/

/-! ### Data-first geometric cycle class (ClosedSubmanifoldData) -/

-- `cycleClass_geom_data` is defined in `Hodge/Classical/GAGA.lean` (in `SignedAlgebraicCycle` namespace).
-- We define a standalone version for `ClosedSubmanifoldData` if needed, or use the one from GAGA.
-- GAGA defines `SignedAlgebraicCycle.cycleClass_geom_data` which takes a cycle.
-- We need one that takes `ClosedSubmanifoldData`.

/-- Geometric cycle class from explicit `ClosedSubmanifoldData`. -/
def cycleClass_geom_data_standalone {p : ℕ}
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    DeRhamCohomologyClass n X (2 * p) :=
  ofForm (CycleClass.fundamentalClassImpl_data_fromCurrents n X p data)
    (CycleClass.fundamentalClassImpl_data_isClosed_ofCurrents n X p data)

/-! ## The Bridge Theorem -/

/-! ### Data-first spine bridge (ClosedSubmanifoldData) -/

-- `SpineBridgeData_data` is defined in `Hodge/Classical/GAGA.lean`.

/-! ### Data-first bridge corollaries -/

theorem spine_bridge_data
    [ChowGAGAData n X] {p : ℕ}
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    [SignedAlgebraicCycleSupportData n X p]
    [SpineBridgeData_data n X p]
    (γ : SmoothForm n X (2 * p)) (hγ_closed : IsFormClosed γ)
    (_hγ_cone : isConePositive γ)
    (Z : SignedAlgebraicCycle n X p)
    (h_from_spine : Z.representingForm = γ) :
    Z.cycleClass_geom_data = ofForm γ hγ_closed := by
  -- By data-first spine bridge: cycleClass_geom_data = ofForm representingForm
  have h1 := SpineBridgeData_data.fundamental_eq_representing
    (n := n) (X := X) (p := p) (Z := Z)
  -- Substitute representing form.
  subst h_from_spine
  -- Close by proof irrelevance of `ofForm`.
  simpa using h1

theorem spine_bridge_data_with_data
    [ChowGAGAData n X] {p : ℕ}
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    [SignedAlgebraicCycleSupportData n X p]
    [SpineBridgeData_data n X p]
    (γ : SmoothForm n X (2 * p)) (hγ_closed : IsFormClosed γ)
    (_hγ_cone : isConePositive γ)
    (Z : SignedAlgebraicCycle n X p)
    (h_from_spine : Z.representingForm = γ)
    (dataZ : ClosedSubmanifoldData n X (2 * p))
    (hdataZ : dataZ = SignedAlgebraicCycle.support_data (n := n) (X := X) (p := p) Z) :
    Z.cycleClass_geom_data = ofForm γ hγ_closed := by
  have h := spine_bridge_data (n := n) (X := X) (p := p)
    γ hγ_closed _hγ_cone Z h_from_spine
  exact h

/-! ## Full Spine Theorem -/

/-- **Full TeX Spine (Data-First)**: Cone-positive Hodge class is algebraic.

    This variant threads explicit `ClosedSubmanifoldData` through the bridge:
    `cycleClass_geom_data` is the proof-track geometric class.

    **Assumptions**: Requires `SpineBridgeData_data` together with the data-first
    PD interface and support data. -/
theorem tex_spine_full_data
    [AutomaticSYRData n X]
    [ChowGAGAData n X] {p : ℕ}
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    [SignedAlgebraicCycleSupportData n X p]
    [SpineBridgeData_data n X p]
    [CalibratedCurrentRegularityData n X (2 * (n - p))]
    [HarveyLawsonKingData n X (2 * (n - p))]
    (γ : SmoothForm n X (2 * p)) (hγ_closed : IsFormClosed γ)
    (hγ_rational : isRationalClass (ofForm γ hγ_closed))
    (hγ_cone : isConePositive γ) :
    ∃ (Z : SignedAlgebraicCycle n X p),
      Z.cycleClass_geom_data = ofForm γ hγ_closed := by
  -- Use the data-first cone-positive construction (returns explicit support data).
  obtain ⟨Z, dataZ, hZ_form, hdataZ⟩ :=
    cone_positive_produces_cycle_support_data_eq
      (n := n) (X := X) (p := p) γ hγ_closed hγ_rational hγ_cone
  use Z
  -- hZ_form : Z.representingForm = γ
  -- hdataZ : dataZ = SignedAlgebraicCycle.support_data Z
  -- Use data-first spine bridge with explicit support data.
  exact spine_bridge_data_with_data (n := n) (X := X) (p := p)
    γ hγ_closed hγ_cone Z hZ_form dataZ hdataZ

end Hodge.TexSpine.GeometricCycleClass
