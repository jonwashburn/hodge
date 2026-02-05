# Multi‑Agent Work Plan (Local, Manual Orchestration)

This repo is running in a **single Codex session**, so we can’t spawn true concurrent agents here.
To parallelize anyway, we’ll run a **manual multi‑agent workflow** where each agent (human or
separate Codex/Cursor session) picks a tightly scoped task, follows the playbook, and checks in
with a short report.

## Autonomy Override (2026-02-04)

Long‑session autonomy is active. Default behavior is **no check‑ins** and continuous execution
until blocked. The check‑in template below is only used if explicitly requested.

## Primary Reference (paper)

- **Primary proof narrative**: `JA_hodge_approach_with_added_refs_blueCites.tex`.
- **Additional narrative**: `final-1-15-milan-05.tex` (Jan 15, 2026).

Any proof‑spine decisions should cite these.

## Non‑Negotiables (from playbook)

- No `sorry`, `axiom`, or `opaque` in proof‑track `Hodge/`.
- No semantic stubs (`:= 0`, `True`, `Set.univ` stand‑ins, etc.).
- Do **not** weaken theorem statements.
- Do **not** edit audit scripts.
- Before any `lake build`: run `lake exe cache get`.

## Agent Rules (scope + safety)

- Keep scope small: 1–2 files, 1–3 lemmas, no semantic definition changes.
- Don’t touch proof‑spine theorem statements unless explicitly assigned.
- Use explicit data interfaces (`ClosedSubmanifoldData`, `OrientedRectifiableSetData`,
  `SubmanifoldIntegrationData`) rather than legacy typeclass binders.

## Check‑In Template (paste in PR / message)

```
Task:
Files touched:
Summary of changes:
No semantic changes (confirm):
Commands run:
Notes / blockers:
```

## Local Integration Checklist (Integrator)

1. Rebase or cherry‑pick agent patches.
2. Run:
   - `lake exe cache get`
   - `lake build <touched modules>`
3. Update `docs/PROOF_COMPLETION_PLAN_FULL_UNCONDITIONAL.md` with deltas.

## Task Queue

See `docs/AGENTS_TASKS.md`.
