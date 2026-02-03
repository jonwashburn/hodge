# Deep Track: Complete Task Index

This document lists **every `sorry` goal** in the deep track, organized by pillar.
Agents should work through these in dependency order.

**Build command**: `lake build Hodge.Deep`

---

## Priority 1: Stokes (Submanifold Integration)

**File**: `Hodge/Deep/Pillars/Stokes.lean`
**Replaces**: explicit `SubmanifoldIntegrationData` (data‑first integration layer)

| Goal | Type | Dependencies |
|------|------|--------------|
| `hausdorff_measure_finite_on_submanifold` | theorem | Mathlib measure theory |
| `realSubmanifoldIntegral` | def | Goal 1.1 |
| `realSubmanifoldIntegral_linear` | theorem | Goal 2.1 |
| `realSubmanifoldIntegral_bound` | theorem | Goal 2.1 |
| `stokes_closed_submanifold` | theorem | Goals 2.1-2.3 |
| `SubmanifoldIntegration.real` | instance | All above |

**Mathlib dependencies**:
- `MeasureTheory.hausdorffMeasure`
- `Geometry.Manifold.MFDeriv`
- `MeasureTheory.Integral.Lebesgue`

---

## Priority 2: Microstructure (SYR Construction)

**File**: `Hodge/Deep/Pillars/Microstructure.lean`
**Replaces**: `AutomaticSYRData.universal`, `CubulationExists.universal`

| Goal | Type | Dependencies |
|------|------|--------------|
| `cubulation_strong_exists` | theorem | Compactness of X |
| `local_sheet_exists` | theorem | Stokes pillar |
| `gluing_boundary_bound` | theorem | Goals 1, 2 |
| `calibration_defect_mesh_bound` | theorem | Goals 1-3 |
| `calibration_defect_tends_to_zero` | theorem | Goal 4.1 |
| `AutomaticSYRData.real` | instance | All above |

**Key insight**: The calibration defect bound is `O(mesh)` where mesh → 0.

---

## Priority 3: Harvey-Lawson (Structure Theorem)

**File**: `Hodge/Deep/Pillars/HarveyLawson.lean`
**Replaces**: `HarveyLawsonKingData.universal`

| Goal | Type | Dependencies |
|------|------|--------------|
| `calibrated_current_support_analytic` | theorem | Stokes pillar |
| `harvey_lawson_decomposition` | theorem | Goal 1.1 |
| `king_algebraicity` | theorem | Goals 1-2, GAGA |
| `HarveyLawsonKingData.real` | instance | All above |

**TeX Reference**: Harvey-Lawson "Calibrated Geometries" (1982)

---

## Priority 4: GAGA (Chow Theorem)

**File**: `Hodge/Deep/Pillars/GAGA.lean`
**Replaces**: `ChowGAGAData.universal`

| Goal | Type | Dependencies |
|------|------|--------------|
| `isAnalyticSet_implies_isAnalyticSetZeroLocus` | theorem | Cartan coherence |
| `IsAlgebraicSetStrong` | structure | Definition only |
| `chow_theorem_strong` | theorem | Goals 1-2 |
| `ChowGAGAData.real` | instance | Goal 3 |

**TeX Reference**: Chow (1949), Serre GAGA (1956)

---

## Priority 5: Federer-Fleming (Compactness)

**File**: `Hodge/Deep/Pillars/FedererFleming.lean`
**Replaces**: `FlatLimitCycleData.universal`

| Goal | Type | Dependencies |
|------|------|--------------|
| `flatNormReal` | def | Infimum over decompositions |
| `flatNormReal_nonneg` | theorem | Goal 1.1 |
| `flatNormReal_triangle` | theorem | Goal 1.1 |
| `federer_fleming_compactness_real` | theorem | Goals 1.1-1.2 |
| `flat_limit_of_cycles_is_cycle_real` | theorem | Goals 1-2 |
| `FlatLimitCycleData.real` | instance | All above |

**TeX Reference**: Federer-Fleming (1960), Federer GMT §4.2.17

---

## Priority 6: Poincaré Duality (Fundamental Class)

**File**: `Hodge/Deep/Pillars/PoincareDuality.lean`
**Replaces**: `SpineBridgeData.universal`

| Goal | Type | Dependencies |
|------|------|--------------|
| `integrationCurrent` | def | Stokes pillar |
| `integrationCurrent_isCycle` | theorem | Goal 1.1 |
| `poincare_dual_form_exists` | theorem | Goals 1.1-1.2 |
| `spine_bridge` | theorem | Harvey-Lawson, GAGA |
| `SpineBridgeData.real` | instance | All above |

---

## Dependency Graph

```
Stokes ←─────────────────────────────────────────┐
   │                                              │
   ▼                                              │
Microstructure ──────────────────────┐            │
   │                                 │            │
   ▼                                 │            │
Harvey-Lawson ─────────┐             │            │
   │                   │             │            │
   ▼                   ▼             ▼            │
GAGA ←─────────────────┴─────────────┘            │
   │                                              │
   ▼                                              │
Federer-Fleming ←────────────────────────────────┤
   │                                              │
   ▼                                              │
Poincaré Duality ←────────────────────────────────┘
```

---

## Completion Checklist

- [ ] `Hodge.Deep.Pillars.Stokes` - 6 sorries
- [ ] `Hodge.Deep.Pillars.Microstructure` - 6 sorries
- [ ] `Hodge.Deep.Pillars.HarveyLawson` - 4 sorries
- [ ] `Hodge.Deep.Pillars.GAGA` - 3 sorries
- [ ] `Hodge.Deep.Pillars.FedererFleming` - 6 sorries
- [ ] `Hodge.Deep.Pillars.PoincareDuality` - 5 sorries

**Total**: ~30 sorries to eliminate for full mathematical completion.

---

## Verification

```bash
# Count remaining sorries
grep -r "sorry" Hodge/Deep/Pillars/ --include="*.lean" | grep -v "Status" | wc -l

# Check axiom status
lake build Hodge.Deep.Audit
```

When all `.real` instances have axioms `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`), the proof is mathematically complete.
