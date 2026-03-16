# Hodge Conjecture Formalization — Progress Tracker

**Last updated**: 2026-03-16
**Branch**: `main` (merged from `claude/hodge-conjecture-proof-VSeH8`)

## Current State

`hodge_conjecture_data` compiles with:
- **Zero sorry** on critical path
- **Zero custom axioms** — depends only on `[propext, Classical.choice, Quot.sound]`
- **10 deep theorem axioms** in Impl files (named mathematical results)
- AxiomGuard compile-time verification passes

## Goal

Replace the 10 axioms with real proofs, making the formalization fully unconditional.

## The 10 Axioms

| # | Axiom | File | Difficulty | Status |
|---|-------|------|-----------|--------|
| 1 | `algebraic_codimension_of_cycle_support` | AlgebraicSupportImpl | EASY | OPEN |
| 2 | `regularized_integration_current_empty` | CurrentRegularizationImpl | EASY | OPEN |
| 3 | `regularized_integration_current_closed` | CurrentRegularizationImpl | MEDIUM | OPEN |
| 4 | `algebraic_subvariety_admits_closed_submanifold_data` | AlgebraicSupportImpl | MEDIUM | OPEN |
| 5 | `spine_bridge_cohomology_eq` | SpineBridgeImpl | HARD | OPEN |
| 6 | `current_regularization_exists` | CurrentRegularizationImpl | HARD | OPEN |
| 7 | `microstructure_syr_existence` | MicrostructureImpl | VERY HARD | OPEN |
| 8 | `calibrated_support_is_analytic` | HarveyLawsonImpl | VERY HARD | OPEN |
| 9 | `chow_theorem_algebraicity` | GAGAImpl | VERY HARD | OPEN |
| 10 | `federer_fleming_compactness` | FedererFlemingImpl | VERY HARD | OPEN |

## Completed Work

| Date | Agent | What | Result |
|------|-------|------|--------|
| 2026-02-05 | claude-session | Replace 9 sorry with 6 axioms | Proof track sorry-free |
| 2026-02-06 | claude-session | Fix build errors, add 4 more axioms | 10 axioms total, all builds pass |
| 2026-02-06 | claude-session | Remove WIP imports from critical path | Zero WIP deps in critical path |
| 2026-02-06 | claude-session | Add PoincareDualityFromCurrentsData via axioms | Clean instance chain |
| 2026-03-16 | cursor-session | Tighten WIP pullback/current-pushforward signatures to require `ContMDiff` | Regularization scaffolding no longer treats arbitrary maps as smooth; targeted WIP build passes |
| 2026-03-16 | cursor-session | Prove chart-level pullback smoothness and route `SmoothForm` pullback through `ContMDiffForm.pullback` | Eliminated the WIP pullback sorries; targeted pullback files, dependency check, and full build pass |
| 2026-03-16 | cursor-session | Refactor the active proof spine to require `SignedAlgebraicCycleSupportData` directly | Removed the codimension-based support binders from `HodgeConjectureAssumptions` and the main bridge theorems; full build and dependency check still pass |
| 2026-03-16 | cursor-session | Replace fake Euclidean current scaffolding with a `TestForm`-based local current interface | Added `Hodge/WorkInProgress/GMT/LocalCurrents.lean`, rebuilt chart pushforward/mollifier wrappers on honest compactly supported test forms, and deleted the placeholder `EuclideanManifold` instances |

## Failed Approaches (DO NOT REPEAT)

| Date | What Was Tried | Why It Failed |
|------|---------------|---------------|
| 2026-02-06 | Prove `spine_bridge_cohomology_eq` | `CurrentRegularizationData` provides no cohomological guarantee — just gives *a* smooth form with no relation to the input current's cohomology class. Would need de Rham theorem. |
| 2026-02-06 | Use `AutomaticSYRData.universal` | Never existed. Use `inferInstance` instead. |
| 2026-02-06 | Import `GMT.MollifierRegularization` for PD | WIP file with sorry. Created axiom-based instance instead. |
| 2026-03-16 | Bundle pullback of forms along arbitrary `f : X → Y` as smooth | Mathematically wrong. Fixed by requiring explicit `hf : ContMDiff ... f` and proving chart-level pullback smoothness under `HasLocallyConstantCharts`. |
| 2026-03-16 | Refactor chartwise regularization by replacing `Current n (TangentModel n) k` with a model-space current only | Still blocked by a deeper modeling issue: the existing `SmoothForm` norm/comass infrastructure requires `CompactSpace`, so the current pushforward-to-chart API cannot be made honest without introducing a local/compactly-supported chart test-form space or a generalized local-current interface. |
| 2026-03-16 | Treat `algebraic_codimension_of_cycle_support` as a routine theorem under current `AlgebraicSubvariety` | Source shows `AlgebraicSubvariety.codim` is unconstrained metadata, so support codimension is not carrier-determined. This requires a modeling refactor, not just a proof. |
| 2026-03-16 | Keep `AlgebraicSubvarietyClosedSubmanifoldData` + `SignedAlgebraicCycleSupportCodimData` on the active proof spine | Semantically weaker than the already-existing direct `SignedAlgebraicCycleSupportData` interface. The spine now depends on the direct support-data binder instead; the codimension-based route remains an off-spine derivation path. |

## Architecture

```
Hodge/Main.lean
  └── hodge_conjecture_data [HodgeConjectureAssumptions n X p]
        └── hodge_conjecture' (Hodge/Kahler/Main.lean)

Instances provided by Hodge/Deep/Pillars/*Impl.lean:
  AlgebraicSupportImpl   → 2 axioms (submanifold data, codimension)
  HarveyLawsonImpl       → 1 axiom  (calibrated support regularity)
  GAGAImpl               → 1 axiom  (Chow's theorem)
  FedererFlemingImpl      → 1 axiom  (compactness)
  MicrostructureImpl      → 1 axiom  (SYR construction)
  SpineBridgeImpl         → 1 axiom  (cohomology bridge)
  CurrentRegularizationImpl → 3 axioms (regularization, closedness, empty)
  HodgeConjectureAssumptionsImpl → assembles all instances
```
