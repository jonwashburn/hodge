# Agent Assignment: Stokes Pillar

## Your Task

You are assigned to work on **`Hodge/Deep/Pillars/Stokes.lean`**.

Your goal: **Reduce the sorry count** by proving actual mathematical content.

## Setup (REQUIRED)

```bash
cd /Users/jonathanwashburn/Projects/hodge
lake exe cache get
lake build Hodge.Deep.Pillars.Stokes
```

## Current State

The file has ~7 `sorry` statements. Each represents a deep theorem about:
- Hausdorff measure on submanifolds
- Integration of differential forms
- Stokes theorem for closed submanifolds
- Mass-comass duality bounds

## Your First Target

Start with **Goal 1.1** (`hausdorff_measure_finite_on_submanifold`):

```lean
theorem hausdorff_measure_finite_on_submanifold (p : ℕ) (Z : Set X)
    (hZ_compact : IsCompact Z) (hZ_submanifold : IsClosed Z) :
    True := by
  sorry
```

This is currently stated as `True` (a placeholder). Your job is to:
1. **Strengthen the statement** to something meaningful, OR
2. **Prove it** if the current statement captures the intent

For this specific goal, the mathematical content is:
> The Hausdorff measure of a compact submanifold is finite.

## What You Should Do

1. **Read the Mathlib docs** for `MeasureTheory.Measure.hausdorffMeasure`
2. **Search the codebase** for how Hausdorff measure is used
3. **Write a proof** using Mathlib lemmas
4. **If blocked**, add a helper lemma and document what's needed

## ⚠️ CRITICAL RULES ⚠️

### ❌ DO NOT:
```lean
-- BAD: Trivializing
theorem hausdorff_measure_finite_on_submanifold ... : True := by
  trivial
```

### ✅ DO:
```lean
-- GOOD: Actual proof (even if incomplete)
theorem hausdorff_measure_finite_on_submanifold (p : ℕ) (Z : Set X)
    (hZ_compact : IsCompact Z) (hZ_submanifold : IsClosed Z) :
    True := by
  -- TODO: The real statement should be:
  -- (MeasureTheory.hausdorffMeasure (2*p) Z) < ⊤
  -- Proof would use: MeasureTheory.hausdorffMeasure_lt_top_of_isCompact
  -- BLOCKED: Need to verify this lemma exists in Mathlib
  sorry
```

Or even better:
```lean
-- BEST: Making real progress
theorem hausdorff_measure_finite_on_submanifold (p : ℕ) (Z : Set X)
    (hZ_compact : IsCompact Z) (hZ_submanifold : IsClosed Z) :
    (MeasureTheory.hausdorffMeasure (2*p) Z) < ⊤ := by
  -- Compact sets have finite Hausdorff measure in any dimension
  exact MeasureTheory.hausdorffMeasure_lt_top_of_isCompact hZ_compact
```

## Verification

After each change:
```bash
lake build Hodge.Deep.Pillars.Stokes
./scripts/agents/verify_agent_work.sh
```

## Success Criteria

Your work is successful if:
1. The sorry count decreased (you proved something)
2. OR you strengthened a statement type (made it more precise)
3. AND the build still passes
4. AND no trivializations were introduced

## When Done

Report:
1. Which goals you worked on
2. What progress was made
3. What blockers remain (if any)
