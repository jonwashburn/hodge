# Autonomy Runway (Long-Session Mode)

This document is the **live execution map** for multi‑hour, uninterrupted sessions.
It is optimized for maximum autonomy while preserving the no‑gotchas constraints.

## Autonomy Contract (No Check‑Ins)

I will proceed without asking and keep working until blocked by:
1. A hard permission error outside the repo.
2. A conflict with the no‑gotchas rules (new axiom/opaque/sorry, or weakened audits).
3. A required change to a **proof‑track theorem statement** that would alter meaning.

If blocked, I will stop and request input. Otherwise I will keep going.

## Primary Objective (Data‑First Proof Spine Only)

Make the data‑first pipeline the **only** proof‑track path:
`ClosedSubmanifoldData → integrationCurrent_data → regularize → PD form → cycle class`.

Compatibility wrappers remain only for legacy call sites and must **not** be used on
the proof track.

## Long‑Session Phases (Run in Order)

### Phase A — Data‑First Hygiene
1. Remove compatibility wrappers from proof‑track call sites.
2. Ensure PD/cycle‑class bridges use `*_data` and explicit `ClosedSubmanifoldData`.
3. Normalize proof‑track docs to data‑first language only.

### Phase B — PD Regularization Plumbing
1. Wire `PoincareDualityFromCurrentsData → PoincareDualFormFromCurrentData`.
2. Implement `CurrentRegularizationLemmas` targets in the new scaffolding.
3. Require the PD form to be obtained by regularizing `integrationCurrent_data`.

### Phase C — Stokes / Integration Tightening
1. Thread `ClosedSubmanifoldData` into remaining Stokes/integration sites.
2. Replace any set‑based Stokes assumptions on the proof spine.

### Phase D — Deep Binder Elimination
1. Remove one deep binder at a time (priority: PD regularization, HL→algebraic, Chow/GAGA).
2. Keep a concrete lemma checklist per binder in the proof plan.

## Audit Cadence (Auto‑Run)

Run at phase boundaries or after significant refactors:
- `./scripts/audit_practical_unconditional.sh`
- `./scripts/audit_stubs.sh --full`
- `lake env lean Hodge/Utils/DependencyCheck.lean`

## Session Output Policy

No intermediate reports. I will only surface a summary if explicitly asked
or if blocked.
