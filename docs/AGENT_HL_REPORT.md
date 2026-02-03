# Agent Harvey–Lawson / Regularity Report (2026‑02‑03)

## Scope
- `Hodge/Classical/HarveyLawson.lean`
- `Hodge/Classical/HarveyLawsonReal.lean`
- `Hodge/AlgGeom/AnalyticSets.lean`

## Findings
- **Deep binders are explicit and still required**: `CalibratedCurrentRegularityData` and
  `HarveyLawsonKingData` are the real bridge for Harvey–Lawson/King. No real instances exist
  in the non‑quarantine proof track.
- **Call sites**: both binders appear in `Hodge/Kahler/Main.lean` (multiple sections of the main theorem),
  and in `Hodge/Deep/Pillars/HarveyLawson.lean` (deep pillar goals).
- **Analytic sets are defined properly**: `IsAnalyticSet` is now `AlgGeom.IsAnalyticSetZeroLocus`
  (local holomorphic zero locus), not “closed”.

## Deep Binders and Call Sites
- `CalibratedCurrentRegularityData`:
  - Definition: `Hodge/Classical/HarveyLawson.lean` (around `class CalibratedCurrentRegularityData`).
  - Call sites: `Hodge/Kahler/Main.lean` (lines ~319, ~405, ~543, ~596); `Hodge/Deep/Pillars/HarveyLawson.lean`.
- `HarveyLawsonKingData`:
  - Definition: `Hodge/Classical/HarveyLawson.lean` (around `class HarveyLawsonKingData`).
  - Call sites: `Hodge/Kahler/Main.lean` (lines ~320, ~406, ~544, ~597);
    `Hodge/Deep/Pillars/HarveyLawson.lean` (goal stubs).

## Residual Placeholder Checks
- `Set.univ` placeholders: only in **quarantine** modules (e.g., `Hodge/Quarantine/Classical/HarveyLawson.lean`);
  no `Set.univ`‑support placeholder remains on the proof track.

## Files / Lines Scanned
- `Hodge/Classical/HarveyLawson.lean`
- `Hodge/Classical/HarveyLawsonReal.lean`
- `Hodge/AlgGeom/AnalyticSets.lean`
- `Hodge/Kahler/Main.lean` (binder call sites)

## Next Steps
- Provide a real `CalibratedCurrentRegularityData` instance from GMT regularity.
- Prove the Harvey–Lawson/King decomposition and attach a non‑quarantine
  `HarveyLawsonKingData` instance.
