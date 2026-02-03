# Agent Task Queue (Parallelizable)

All tasks follow `docs/AGENT_PLAYBOOK_FULL_UNCONDITIONAL.md`.
Keep scope tight and avoid semantic definition changes.

## AG‑A — Remove remaining `ClosedSubmanifoldStokesData` binders in GMT call sites

- **Goal**: Replace wrapper usage with explicit `ClosedSubmanifoldData` in proof‑track files.
- **Targets**:
  - `Hodge/GMT/PoincareDuality.lean` (bridge helpers)
  - `Hodge/GMT/IntegrationCurrent.lean` (callers outside the data‑first section)
  - Any call sites found via `grep -RIn --include="*.lean" "ClosedSubmanifoldStokesData" Hodge/`
- **Deliverable**: data‑first versions + thin wrappers retained only where needed.

## AG‑B — Remove remaining legacy `SubmanifoldIntegration` binders

- **Goal**: Use `SubmanifoldIntegrationData` explicitly in callers.
- **Targets**:
  - `Hodge/Analytic/Integration/TopFormIntegral.lean` (already data‑first; check callers)
  - Any call sites found via `grep -RIn --include="*.lean" "SubmanifoldIntegration" Hodge/`
- **Deliverable**: all proof‑track code uses explicit data; wrapper class remains only for compatibility.

## AG‑C — Tighten Stokes/integration docs to match data‑first pipeline

- **Goal**: Remove stale mentions of `setIntegral` / legacy set‑based stubs.
- **Targets**:
  - `Hodge/GMT/IntegrationCurrent.lean` docstrings
  - `Hodge/Analytic/Integration/HausdorffMeasure.lean` comments
  - `Hodge/Analytic/Currents.lean` top‑level documentation

## AG‑D — Plan updates (deltas)

- **Goal**: Keep the plan in sync with each tightening step.
- **Targets**:
  - `docs/PROOF_COMPLETION_PLAN_FULL_UNCONDITIONAL.md`
- **Deliverable**: add dated bullet(s) in “Recent Deltas”.

