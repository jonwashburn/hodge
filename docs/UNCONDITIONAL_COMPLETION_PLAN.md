# Unconditional completion plan (no deep typeclass assumptions)

## Autonomy Update (2026-02-04)

Long-session autonomy is active. The proof track is **data‑first** and does **not**
use compatibility wrappers. Deep binders will be eliminated by **real constructions**,
not by trivial universal instances.

## Goal

Make the **public entrypoint** `Hodge/Main.lean:hodge_conjecture` compile and be usable **without**
requiring proof-track typeclass assumptions like:

- `SubmanifoldIntegration`
- `AutomaticSYRData`
- `FlatLimitCycleData`
- `HarveyLawsonKingData`
- `ChowGAGAData`
- `CycleClass.PoincareDualityFromCurrentsData` (proof‑track binder; yields
  `PoincareDualFormFromCurrentData` as a derived instance)
- `SpineBridgeData_data`

In other words: `hodge_conjecture` should have only the ambient manifold hypotheses (the ones already
in `Hodge/Main.lean`’s `variable` block) and Lean should fill in everything else via **universal
instances**.

## Current blockers (dependency-cone gaps)

These are the only items that prevent “fully unconditional with universal instances” (they are
explicitly called out in `docs/PROOF_TRACK_STATUS.md`):

1. **`Hodge/Kahler/Main.lean`**: `AutomaticSYRData.universal` contains a `sorry` (reported as
   `sorryAx` when instantiated).
2. **`Hodge/Classical/GAGA.lean`**: `SpineBridgeData_data.universal` is implemented via a global `axiom`
   (`fundamental_eq_representing_axiom`).

Additionally, to actually *use* `hodge_conjecture_data` without assumptions, we need missing universal
instances:

3. **`Hodge/Analytic/Integration/HausdorffMeasure.lean`**: no concrete
   `SubmanifoldIntegrationData` exists yet (data‑first integration is still an interface).
4. **`Hodge/Classical/GAGA.lean`**: no `ChowGAGAData.universal` instance exists.

## Execution plan

### A. Provide **real** instances (no stubs, no axioms)

- **Submanifold integration** in
  `Hodge/Analytic/Integration/HausdorffMeasure.lean` must be realized with genuine
  Hausdorff integration data (no `:= 0` placeholders).

- **Chow/GAGA** in `Hodge/Classical/GAGA.lean` must be proved (analytic → algebraic).

### B. Remove `sorryAx` from `AutomaticSYRData.universal`

- Must be replaced by a **real microstructure construction** (no zero‑current shortcut).

### C. Remove the custom axiom from `SpineBridgeData_data.universal`

- Prove the real bridge (fundamental class equals representing form) via
  de Rham representability + Harvey–Lawson (no axioms, no aliases).

### D. Make the public theorem statement truly unconditional

- Edit `Hodge/Main.lean`:
  - Remove all proof-track typeclass binders from `theorem hodge_conjecture`.
  - Leave the proof as a direct call to `hodge_conjecture_data`; universal instances should resolve.

## Verification checklist

Run (repo rule: **always** fetch cache before building):

```bash
./scripts/build.sh
lake env lean Hodge/Utils/DependencyCheck.lean
```

And sanity-check:

- `#print axioms hodge_conjecture` contains **no** `sorryAx`
- `#print axioms AutomaticSYRData.universal` contains **no** `sorryAx`
- no custom axioms remain on the `hodge_conjecture` dependency cone
