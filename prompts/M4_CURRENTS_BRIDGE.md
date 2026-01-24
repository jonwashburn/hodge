# M4: Currents/Integration Bridge to Real Measure Theory

**Re-queue this prompt until the checkbox is checked.**

## Cursor Notes

```
# Hodge Conjecture Lean 4 Formalization

## CRITICAL: Mathlib Cache (NEVER rebuild Mathlib from source!)
Before running ANY `lake build` command, ALWAYS run:
  lake exe cache get

## Build Commands
  ./scripts/build.sh           # Safe build with cache
  lake env lean <file.lean>    # Check single file
  lake build Hodge.Kahler.Main # Build main theorem

## Verification Commands
  lake env lean Hodge/Utils/DependencyCheck.lean  # Check axioms
  ./scripts/audit_stubs.sh                        # Audit for stubs/sorries

## Key Files for This Task
  - Hodge/Analytic/Currents.lean           # Current infrastructure
  - Hodge/Analytic/IntegralCurrents.lean   # Integral currents
  - Hodge/GMT/PoincareDuality.lean         # GMT bridge
  - Hodge/Analytic/Integration/            # Integration infrastructure
  - Mathlib.MeasureTheory.*                # Mathlib measure theory
```

## Current State (PLACEHOLDERS)

The current/integration infrastructure has several placeholder definitions:

### In `Hodge/Analytic/Currents.lean`:

```lean
-- integration_current is defined but uses placeholder integration
structure IntegrationData ... where
  bdryMass : ℝ≥0
  stokes_bound : True    -- ❌ PLACEHOLDER (should be actual Stokes bound)

-- The actual integration is via a placeholder
def integration_current ... :=
  { toFun := fun ω => submanifoldIntegral ...   -- Uses placeholder integration
    boundary_bound := ... }
```

### In `Hodge/Analytic/Integration/`:

```lean
-- L2Inner_measure is real (uses Bochner integral) ✓
-- But the connection to currents/PD forms is not established
```

## What It Should Be

For M1-M3 to be semantically meaningful, we need:

1. **Integration currents** that actually integrate forms over submanifolds
   - `[Z](ω) = ∫_Z ω` using real measure-theoretic integration

2. **Connection to cohomology**
   - The de Rham current `[ω]` induced by a form
   - The integration current `[Z]` induced by a subvariety
   - Proof that these live in the same cohomology space

3. **Stokes theorem** (at least for closed submanifolds)
   - `[Z](dω) = [∂Z](ω)` → `[Z](dω) = 0` when ∂Z = ∅

## Key Mathlib Infrastructure

```lean
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.IntegrableOn

-- Hausdorff measure for submanifolds
MeasureTheory.Measure.hausdorffMeasure

-- Integration over measurable sets
MeasureTheory.integral_indicator
MeasureTheory.set_integral_eq_subsingleton
```

## Approach Options

### Option A: Minimal bridge (axiomatize key properties)
Keep placeholders but add axioms stating the key properties (integration = actual integral, 
Stokes holds). This unblocks M1-M3 without full measure theory.

### Option B: Connect to Mathlib measures incrementally
1. Define `submanifoldMeasure` using Hausdorff measure
2. Define `integrationCurrentReal` using `∫ ω dμ` 
3. Prove basic properties (linearity, continuity)

### Option C: Full GMT formalization
Build the complete geometric measure theory stack (months of work).

## Definition of Done

- [ ] `integration_current` connects to real Mathlib integration (or axiomatizes this)
- [ ] The `stokes_bound` field is non-trivial for closed submanifolds
- [ ] There's a path from `[Z]` (integration current) to cohomology classes
- [ ] `lake build Hodge.Kahler.Main` succeeds
- [ ] `lake env lean Hodge/Utils/DependencyCheck.lean` shows only standard axioms

## Relationship to Other MUST-HAVEs

- **M1** needs currents to represent the Harvey-Lawson output
- **M2** needs integration to define Poincaré dual forms
- **M3** needs the cycle→cohomology map to be non-trivial

M4 is foundational—progress here unblocks the other items.

## Progress Log

(Add entries as you work)

- [ ] Started investigation
- [ ] Surveyed Mathlib measure theory APIs
- [ ] Identified minimal viable bridge
- [ ] Implemented fix
- [ ] Verified build passes
- [ ] Verified axiom check passes

---
**When this is complete, check off M4 in `docs/REQUEUE_ANALYTIC_HODGE_STACK.md`**
