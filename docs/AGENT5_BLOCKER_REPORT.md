# Agent 5 Blocker Report: GMT / Currents / Compactness

**Agent**: Agent 5 — GMT/Classical  
**Date**: 2026-01-18  
**Scope**: Provide the `Hodge.GMT` module layout referenced by `docs/OPERATIONAL_PLAN_5_AGENTS.md`,
without duplicating the already-existing GMT infrastructure in `Hodge/Analytic/*`.

---

## Executive Summary

The repository already contains substantial GMT infrastructure under:
- `Hodge/Analytic/Currents.lean` (currents + `IntegrationData`)
- `Hodge/Analytic/FlatNorm.lean` (flat norm)
- `Hodge/Analytic/IntegralCurrents.lean` (integral currents)

Agent 5 work therefore focused on **creating the planned `Hodge/GMT/*` module tree** as
thin wrappers/re-exports, so the project matches the operational plan’s file layout
without introducing conflicting duplicate definitions.

---

## Files Created (Agent 5)

### New module umbrella

- `Hodge/GMT.lean`

### Wrappers / compatibility layers

- `Hodge/GMT/Current.lean`
  - Defines `Hodge.GMT.DeRhamCurrent` as a compatibility alias of the project’s `Current`
  - Defines `DeRhamCurrent.boundary` using `Current.boundary` (successor case)

- `Hodge/GMT/IntegrationCurrent.lean`
  - Defines `Hodge.GMT.integrationCurrent` as a wrapper of `_root_.integration_current`
  - Provides `integrationCurrent_empty`

- `Hodge/GMT/FlatNormTopology.lean`
  - Re-exports `_root_.flatNorm` as `Hodge.GMT.flatNorm`

- `Hodge/GMT/IntegralCurrentSpace.lean`
  - Defines `bdryMass` and `BoundedIntegralCurrents` (bounded mass + bounded boundary mass)

### Placeholder API (off-proof-track intent)

- `Hodge/GMT/CurrentToForm.lean`
  - Provides `regularizeCurrentToForm` as a total placeholder (`:= 0`)
  - This is the interface planned for “current → smooth form” regularization

- `Hodge/GMT/PoincareDuality.lean`
  - Re-exports the existing PD-form interface from `Hodge/Classical/CycleClass.lean`

---

## Verification (Executed)

All commands were run from `/Users/jonathanwashburn/Projects/hodge`.

### Build the new GMT module

```bash
lake exe cache get
lake build Hodge.GMT
```

### Proof-track axiom audit (kernel dependencies)

```bash
./scripts/audit_stubs.sh
```

Result: `hodge_conjecture'` depends only on standard Lean axioms:
`propext`, `Classical.choice`, `Quot.sound`.

### Full repo scan (noisy; checks for explicit `axiom` declarations)

```bash
./scripts/audit_stubs.sh --full
```

Result: **No `axiom` declarations** found.

---

## Current “Blockers” / Next Work (Research-Level)

These are the items the operational plan labels as Sprint 2+ Agent 5 work:

- **Real Hausdorff integration currents** (replace `integrate := 0` stubs in `IntegrationData`-based constructors)
- **Regularization / smoothing of currents to forms**
  - `regularizeCurrentToForm` is currently a placeholder
- **Meaningful Poincaré duality construction**
  - Currently `CycleClass.poincareDualFormExists` is a semantic placeholder (returns `0`)
- **Compactness theorems** (Federer–Fleming style)
  - The repo currently has “zero-sequence” compactness lemmas sufficient for the microstructure stubs

These are not needed for the current proof-track status (which is already axiom-minimal),
but are required if/when the development replaces the remaining semantic stubs with real GMT.

