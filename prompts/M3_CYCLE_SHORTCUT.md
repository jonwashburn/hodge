# M3: Remove the "Cycle Carries γ by Definition" Shortcut

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
  - Hodge/Classical/GAGA.lean              # THE FILE TO FIX
  - Hodge/Kahler/Main.lean                 # Uses SignedAlgebraicCycle
  - Hodge/Classical/CycleClass.lean        # FundamentalClassImpl
```

## Current State (SEMANTIC SHORTCUT)

**File**: `Hodge/Classical/GAGA.lean` (lines 391-418)

```lean
structure SignedAlgebraicCycle (n : ℕ) (X : Type u) (p : ℕ) ... where
  pos : Set X
  neg : Set X
  pos_alg : isAlgebraicSubvariety n X pos
  neg_alg : isAlgebraicSubvariety n X neg
  representingForm : SmoothForm n X (2 * p)           -- ❌ SHORTCUT
  representingForm_closed : IsFormClosed representingForm

-- The cycle class is DEFINED as the quotient of the carried form
noncomputable def SignedAlgebraicCycle.cycleClass {p : ℕ}
    (Z : SignedAlgebraicCycle n X p) : DeRhamCohomologyClass n X (2 * p) :=
  ⟦Z.representingForm, Z.representingForm_closed⟧    -- ❌ BY DEFINITION

-- RepresentsClass is then rfl
def SignedAlgebraicCycle.RepresentsClass {p : ℕ} (Z : SignedAlgebraicCycle n X p)
    (η : DeRhamCohomologyClass n X (2 * p)) : Prop :=
  Z.cycleClass = η                                    -- ❌ TRIVIALLY TRUE when γ is carried
```

## Why This Is a Problem

In `Hodge/Kahler/Main.lean:cone_positive_produces_cycle` (lines 254-269):

```lean
let Z : SignedAlgebraicCycle n X p := {
  pos := Zpos,
  neg := ∅,
  ...
  representingForm := γ,              -- ← The input γ is carried as a field
  representingForm_closed := h_closed
}

use Z
-- Z.RepresentsClass (ofForm γ h_closed) is now rfl because:
-- Z.cycleClass = ⟦Z.representingForm⟧ = ⟦γ⟧ = ofForm γ h_closed
```

This **bypasses the geometric content**: we should be proving `[Z] = [γ]` where `[Z]` 
is derived from the cycle via integration/fundamental class, not by definition.

## What It Should Be

The cycle class should be **computed from the cycle**, not carried as a field:

```lean
structure SignedAlgebraicCycle (n : ℕ) (X : Type u) (p : ℕ) ... where
  pos : Set X
  neg : Set X
  pos_alg : isAlgebraicSubvariety n X pos
  neg_alg : isAlgebraicSubvariety n X neg
  -- NO representingForm field

-- The cycle class is COMPUTED via fundamental class / integration
noncomputable def SignedAlgebraicCycle.cycleClass {p : ℕ}
    (Z : SignedAlgebraicCycle n X p) : DeRhamCohomologyClass n X (2 * p) :=
  -- Use FundamentalClassSet or integration current
  ofForm (fundamentalClassImpl n X p Z.support) ...
```

Then `RepresentsClass` becomes a **theorem to prove**, not `rfl`.

## Approach Options

### Option A: Remove representingForm, compute cycleClass from support
Requires M2 (Poincaré dual) to be non-trivial first.

### Option B: Keep representingForm but add a consistency axiom
Add an axiom: `[Z.support] = [Z.representingForm]` and use it in proofs.

### Option C: Refactor to carry a proof witness
```lean
structure SignedAlgebraicCycle ... where
  ...
  representingForm : SmoothForm n X (2 * p)
  represents_witness : FundamentalClass Z.support = ofForm representingForm ...
```

## Dependencies

This task likely depends on:
- **M2** (Poincaré dual form) for computing `[Z]` from the cycle
- **M4** (currents/integration bridge) for connecting cycles to cohomology

Consider working on M2/M4 first, or implementing Option B as an intermediate step.

## Definition of Done

- [ ] `SignedAlgebraicCycle.cycleClass` is not trivially `⟦Z.representingForm⟧`
- [ ] `Z.RepresentsClass η` requires a non-trivial proof
- [ ] `lake build Hodge.Kahler.Main` succeeds
- [ ] `lake env lean Hodge/Utils/DependencyCheck.lean` shows only standard axioms

## Progress Log

(Add entries as you work)

- [ ] Started investigation
- [ ] Assessed dependencies on M2/M4
- [ ] Identified minimal fix approach
- [ ] Implemented fix
- [ ] Verified build passes
- [ ] Verified axiom check passes

---
**When this is complete, check off M3 in `docs/REQUEUE_ANALYTIC_HODGE_STACK.md`**
