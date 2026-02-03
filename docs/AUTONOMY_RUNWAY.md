# Autonomy Runway (Long-Session Plan)

This document is the **live execution map** for long, uninterrupted sessions. It is intended
to reduce check-ins and allow autonomous progress while preserving the "no-gotchas" constraints.

## Autonomy Rules (No-Ask Defaults)

I will proceed without asking unless an action:
1. Changes theorem statements on the proof track.
2. Introduces any `axiom`/`opaque`/`sorry`.
3. Modifies audit scripts or relaxes audit criteria.
4. Performs destructive operations (delete/move large sections of proof-track code).

If any of the above are necessary, I will stop and ask.

## Primary Objective (Data-First Proof Spine)

The goal is to make the **data‑first pipeline** the default proof track:
`ClosedSubmanifoldData → integrationCurrent_data → regularize → PD form → cycle class`.

## Work Phases (Run in Order)

### Phase A — Data‑First Hygiene
1. Remove remaining compatibility‑wrapper usage in proof‑track call sites.
2. Ensure all PD/cycle‑class bridges use `*_data` and explicit `ClosedSubmanifoldData`.
3. Update any proof‑track docs to use data‑first language.

### Phase B — PD Regularization Plumbing
1. Implement `CurrentRegularizationLemmas` instances where possible.
2. Use `PoincareDualityFromCurrentsData` → `PoincareDualFormFromCurrentData` wiring.
3. Keep regularization scaffolding fully data‑first; no stubs/axioms.

### Phase C — Stokes / Integration Tightening
1. Thread `ClosedSubmanifoldData` into any remaining Stokes/integration call sites.
2. Remove any implicit or set‑based Stokes assumptions from proof‑track lemmas.

### Phase D — Binder Elimination Scaffolding
1. Identify the next binder to eliminate (PD regularization or Harvey–Lawson bridge).
2. Create precise lemma checklists and file scaffolding for that binder.
3. Record blockers in `docs/PROOF_COMPLETION_PLAN_FULL_UNCONDITIONAL.md`.

## Milestone Checks (Lightweight)

I will run audits at **phase boundaries** or after large refactors:
- `./scripts/audit_practical_unconditional.sh`
- `./scripts/audit_stubs.sh --full`
- `lake env lean Hodge/Utils/DependencyCheck.lean`

## Progress Reporting

Each session will end with:
1. What changed (files + key lemmas).
2. What remains (next phase steps).
3. Any blockers (by file/lemma).
