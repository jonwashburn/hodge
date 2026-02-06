# Hodge Conjecture Lean 4 Formalization — Autonomous Agent Prompt

You are an autonomous agent working on the Lean 4 formalization of the Hodge Conjecture.

## Current State (auto-updated)

The main theorem `hodge_conjecture_data` compiles with:
- **Zero sorry** on the critical path
- **Zero custom axioms** — depends only on `[propext, Classical.choice, Quot.sound]`
- **10 deep theorem axioms** in `Hodge/Deep/Pillars/*Impl.lean`

The AxiomGuard at `Hodge/AxiomGuard.lean` verifies this at compile time.

## Your Mission

Reduce the axiom count by replacing axioms with real proofs. Each axiom you eliminate
strengthens the formalization.

## The 10 Axioms (ranked by difficulty)

### Most likely provable
1. `algebraic_codimension_of_cycle_support` (AlgebraicSupportImpl.lean)
   — Codimension uniqueness. May follow from `SignedAlgebraicCycle` structure.

2. `regularized_integration_current_empty` (CurrentRegularizationImpl.lean)
   — Empty carrier → zero form. Should follow from `integrationCurrent_data` being zero for empty carrier.

3. `regularized_integration_current_closed` (CurrentRegularizationImpl.lean)
   — Regularized form is closed. Requires showing regularization commutes with d.

### Hard but well-defined
4. `algebraic_subvariety_admits_closed_submanifold_data` (AlgebraicSupportImpl.lean)
   — Algebraic subvarieties have closed submanifold structure.

5. `spine_bridge_cohomology_eq` (SpineBridgeImpl.lean)
   — Geometric cycle class = representing form class. Requires Poincaré duality.

6. `current_regularization_exists` (CurrentRegularizationImpl.lean)
   — Current → smooth form. Requires mollifier/convolution infrastructure.

### Deep theorems (require major infrastructure)
7. `microstructure_syr_existence` (MicrostructureImpl.lean)
   — SYR microstructure construction. Requires cubulation + calibration.

8. `calibrated_support_is_analytic` (HarveyLawsonImpl.lean)
   — Harvey-Lawson 1982. Calibrated geometry regularity.

9. `chow_theorem_algebraicity` (GAGAImpl.lean)
   — Chow's theorem 1949 / Serre GAGA 1956.

10. `federer_fleming_compactness` (FedererFlemingImpl.lean)
    — Federer-Fleming 1960. Flat norm compactness for integral currents.

## How to Work

1. Read this file and `PROGRESS.md`
2. Check `current_tasks/` for locks
3. Pick the highest-priority unlocked axiom
4. Lock it: `echo "$(date)" > current_tasks/AXIOM_NAME.lock`
5. Read the Impl file and trace the definitions it uses
6. Try to prove the axiom from existing definitions
7. If you prove it, replace the `axiom` with a `theorem`
8. Verify: `~/.elan/bin/lake build Hodge.AxiomGuard`
9. Commit and push to the working branch
10. Remove lock, update PROGRESS.md

## Build Commands

```bash
# Build the axiom guard (full verification)
~/.elan/bin/lake build Hodge.AxiomGuard

# Build a specific module
~/.elan/bin/lake build Hodge.Deep.Pillars.AlgebraicSupportImpl

# Check sorry count in non-WIP files
grep -r "sorry" Hodge/ --include="*.lean" | grep -v WorkInProgress | grep -v archive | grep -v "\.olean" | grep -v "-- " | grep -v "/\*" | wc -l
```

## Rules

1. **Never break the build.** Always verify before committing.
2. **Never introduce new axioms or sorry** on the proof track.
3. **Never modify `Hodge/Main.lean` or `Hodge/Kahler/Main.lean`** without good reason.
4. **Maintain lock discipline.** Check/create/remove locks in `current_tasks/`.
5. **Update PROGRESS.md** after completing work.
6. **If stuck for 30 minutes, try a different axiom.**
7. **Log failed approaches** in PROGRESS.md.

## Key Architecture

| File | Role |
|------|------|
| `Hodge/Main.lean` | Top theorem: `hodge_conjecture_data` |
| `Hodge/Kahler/Main.lean` | Proof logic: `hodge_conjecture'` |
| `Hodge/Deep/Pillars/*Impl.lean` | **YOUR TARGET**: axiom implementations |
| `Hodge/AxiomGuard.lean` | Compile-time axiom checker |
| `Hodge/Classical/*.lean` | Typeclass interfaces (GAGA, CycleClass, etc.) |
| `Hodge/Cohomology/Basic.lean` | `DeRhamCohomologyClass`, `ofForm` |
| `Hodge/Analytic/*.lean` | Forms, currents, calibration |

## Context Window Tips

- Use `grep` to find definitions, don't read entire files
- Build individual modules, not the whole project
- Focus on the **first** error only
- `lake` is at `~/.elan/bin/lake` (may not be on PATH)
