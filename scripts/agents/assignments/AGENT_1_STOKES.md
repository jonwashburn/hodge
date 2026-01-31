# Agent 1: Stokes Pillar

## Setup (REQUIRED FIRST)
```bash
cd /Users/jonathanwashburn/Projects/hodge
lake exe cache get
```

## Your Target
**File**: `Hodge/Deep/Pillars/Stokes.lean`

## Context
Read `scripts/agents/AGENT_CONTEXT.md` for project rules.

## Current State
The file defines Hausdorff measure integration infrastructure. Key goals:
1. `hausdorff_measure_finite_on_compact` - prove Hausdorff measure is finite on compact sets
2. `hausdorff_measure_locally_finite` - prove μH is locally finite
3. `formEvalPairing` - needs real implementation (currently placeholder)
4. `realSubmanifoldIntegral_linear` - blocked on formEvalPairing
5. `realSubmanifoldIntegral_bound` - almost proved, needs integration lemma
6. `stokes_closed_submanifold` - Stokes theorem
7. `SubmanifoldIntegration.real` - full instance (depends on above)

## Priority Tasks
1. **Prove `hausdorff_measure_finite_on_compact`** using Mathlib's Hausdorff measure lemmas
2. **Improve `formEvalPairing`** to be linear in the form (not just ‖ω‖)
3. **Complete `realSubmanifoldIntegral_bound`** proof

## Mathlib Resources
- `MeasureTheory.Measure.hausdorffMeasure`
- `MeasureTheory.setIntegral_const`
- `MeasureTheory.integral_smul`, `MeasureTheory.integral_add`

## ⚠️ RULES
- NEVER use `trivial`, `admit`, `:= True`, `:= ⟨⟩`
- Actually prove using Mathlib lemmas
- Document blockers in comments if stuck
- Run `lake build Hodge.Deep.Pillars.Stokes` after each change

## Verification
```bash
./scripts/agents/verify_agent_work.sh
```

## Success = sorry count decreases OR statements strengthened OR real definitions added
