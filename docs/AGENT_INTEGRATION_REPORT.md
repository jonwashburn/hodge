# Agent F Report — Integration Refactor (Data‑First)

## Scope
- `Hodge/Analytic/Integration/HausdorffMeasure.lean`
- `Hodge/Analytic/Integration/TopFormIntegral.lean`
- `Hodge/GMT/GMTTests.lean`

## Findings (to fill)
### Remaining `SubmanifoldIntegration` usages in proof‑track code
- Only legacy/doc references in deep‑track docs (`Hodge/Deep.*`); no proof‑track code depends on
  the old field‑based class anymore.
- Quarantine files still mention it (intentionally out of proof track).

### Call‑sites updated to explicit `SubmanifoldIntegrationData`
- `Hodge/Analytic/Integration/HausdorffMeasure.lean` (core API now data‑first)
- `Hodge/Analytic/Integration/TopFormIntegral.lean` (top‑form integration + pairings now take data)
- `Hodge/GMT/GMTTests.lean` (test stub updated)

## Risks / Notes
- Threading `SubmanifoldIntegrationData` explicitly will require updating any future callers
  that expect implicit typeclass resolution. A thin wrapper (`SubmanifoldIntegration`) is kept
  for backward compatibility.

## Next steps
- Remove remaining doc references to `SubmanifoldIntegration.universal/real` where misleading.
- Add bridge lemmas that use the wrapper class to produce explicit data as needed.
