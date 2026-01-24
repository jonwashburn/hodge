# M2: Replace Poincaré Dual Form Semantic Stub

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
  - Hodge/Classical/CycleClass.lean        # THE FILE TO FIX
  - Hodge/Classical/GAGA.lean              # Uses poincareDualForm via fundamentalClassImpl
  - Hodge/GMT/PoincareDuality.lean         # Bridge module
  - Hodge/Analytic/Currents.lean           # Current infrastructure
```

## Current State (SEMANTIC STUB)

**File**: `Hodge/Classical/CycleClass.lean` (lines 205-231)

```lean
noncomputable def poincareDualFormExists (n : ℕ) (X : Type u) (p : ℕ) ... (Z : Set X) :=
  by_cases hZ : Z = ∅
  · -- For empty set: returns 0 ✓ (correct)
    ...
  · -- For nonempty Z: returns omegaPower p ❌ (STUB)
    refine
      { form := omegaPower (n := n) (X := X) p    -- ❌ NOT the actual PD form
        is_closed := omegaPower_isClosed ...
        ... }
```

For any non-empty `Z`, this returns `ω^p` (the Kähler power) instead of the actual 
Poincaré dual form of `Z`.

## What It Should Be

The **Poincaré dual form** η_Z of a codimension-p subvariety Z is the unique closed 
2p-form such that:

```
∫_X η_Z ∧ α = ∫_Z α   for all closed (2n-2p)-forms α
```

This should be constructed from:
1. The integration current [Z] over the subvariety
2. de Rham's theorem (currents ↔ cohomology)
3. The Hodge star and L² theory (to get a smooth representative)

**Must become**: Given a set Z, produce:
1. The actual Poincaré dual form η_Z (not just ω^p)
2. Proof that η_Z is closed
3. (Ideally) proof that [η_Z] = fundamental class of Z in cohomology

## Where It's Used

In `Hodge/Classical/CycleClass.lean:fundamentalClassImpl` (line 295):

```lean
def fundamentalClassImpl (n : ℕ) (X : Type u) ... (p : ℕ) (Z : Set X) :=
  CycleClass.poincareDualForm n X p Z
```

This is the definition that backs `FundamentalClassSet` in GAGA.lean.

## Approach Options

### Option A: Return integration-current-based form
Use the `integration_current` infrastructure to define the PD form.

### Option B: Parametric by Z (structure-based)
Have `poincareDualFormExists` take the actual form as a parameter (like `SignedAlgebraicCycle`).

### Option C: Axiomatize existence
Add an axiom asserting PD form existence with the required properties.

## Definition of Done

- [ ] `poincareDualFormExists` returns a Z-dependent form (not `omegaPower p` for all Z)
- [ ] The construction is connected to `Z` in some meaningful way
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
**When this is complete, check off M2 in `docs/REQUEUE_ANALYTIC_HODGE_STACK.md`**
