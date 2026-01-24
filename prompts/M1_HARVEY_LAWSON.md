# M1: Replace Harvey-Lawson Semantic Stub

**Re-queue this prompt until the checkbox is checked.**

## Cursor Notes

```
# Hodge Conjecture Lean 4 Formalization

## CRITICAL: Mathlib Cache (NEVER rebuild Mathlib from source!)
Before running ANY `lake build` command, ALWAYS run:
  lake exe cache get

## Build Commands
  ./scripts/build.sh           # Safe build with cache
  lake env lean <file.lean>    # Check single file
  lake build Hodge.Kahler.Main # Build main theorem

## Verification Commands
  lake env lean Hodge/Utils/DependencyCheck.lean  # Check axioms
  ./scripts/audit_stubs.sh                        # Audit for stubs/sorries

## Key Files for This Task
  - Hodge/Classical/HarveyLawson.lean      # THE FILE TO FIX
  - Hodge/Kahler/Main.lean                 # Uses harvey_lawson_theorem
  - Hodge/Analytic/Currents.lean           # Current infrastructure
  - Hodge/Analytic/IntegralCurrents.lean   # Integral current definitions
```

## Current State (SEMANTIC STUB)

**File**: `Hodge/Classical/HarveyLawson.lean` (lines 367-378)

```lean
def harvey_lawson_theorem {k : ℕ} (_hyp : HarveyLawsonHypothesis n X k) :
    HarveyLawsonConclusion n X k where
  varieties := ∅                    -- ❌ STUB: returns empty set
  multiplicities := fun ⟨_, h⟩ => absurd h (by simp)
  codim_correct := fun _ h => absurd h (by simp)
  represents := fun _ => True       -- ❌ STUB: trivially true
```

This stub **bypasses the geometric content** of the Harvey-Lawson Structure Theorem.

## What It Should Be

The Harvey-Lawson Structure Theorem (1982) states:

> A calibrated integral current on a Kähler manifold is represented by integration over 
> a finite union of complex analytic subvarieties with positive integer multiplicities.

**Must become**: Given a calibrated integral current T, produce:
1. A finite set of analytic subvarieties `{V₁, ..., Vₘ}`
2. Positive multiplicities `{m₁, ..., mₘ}`
3. A proof that `T = Σᵢ mᵢ [Vᵢ]` (as integration currents)

## Where It's Used

In `Hodge/Kahler/Main.lean:cone_positive_produces_cycle` (lines 229-269):

```lean
-- Step 2: Use Harvey-Lawson Structure Theorem to represent the limit as analytic varieties
let hyp : HarveyLawsonHypothesis n X (2 * (n - p)) := { ... }
let hl_concl := harvey_lawson_theorem hyp
```

The `hl_concl.varieties` is currently `∅`, which makes the subsequent `SignedAlgebraicCycle` 
construction vacuous.

## Approach Options

### Option A: Minimal non-trivial stub
Make `varieties` non-empty when `hyp.T` is non-zero, using existing infrastructure.

### Option B: Axiomatize the geometric content
Add an axiom stating the existence result, with the stub becoming a wrapper.

### Option C: Full implementation
Build the actual theory (support decomposition, regularity, analytic structure).

## Definition of Done

- [ ] `harvey_lawson_theorem` no longer returns `varieties := ∅` for non-zero inputs
- [ ] The `represents` predicate is non-trivial (not `fun _ => True`)
- [ ] `lake build Hodge.Kahler.Main` succeeds
- [ ] `lake env lean Hodge/Utils/DependencyCheck.lean` shows only standard axioms

## Progress Log

(Add entries as you work)

- [ ] Started investigation
- [ ] Identified minimal fix approach
- [ ] Implemented fix
- [ ] Verified build passes
- [ ] Verified axiom check passes

---
**When this is complete, check off M1 in `docs/REQUEUE_ANALYTIC_HODGE_STACK.md`**
