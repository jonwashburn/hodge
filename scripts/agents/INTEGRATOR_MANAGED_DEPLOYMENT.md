# Integrator-Managed Agent Deployment

This document describes how the Integrator (Claude) can orchestrate autonomous agents to complete the formalization.

## How It Works

### Mode 1: Direct Work (Fastest)

I (the Integrator) directly:
1. Read a pillar file
2. Identify provable lemmas
3. Write the proof
4. Verify it compiles
5. Commit and push

**Advantage**: No coordination overhead, I can use full context.

### Mode 2: Agent Orchestration (Scalable)

I generate **focused task specifications** for autonomous agents:

```json
{
  "task_id": "stokes-hausdorff-finite",
  "file": "Hodge/Deep/Pillars/Stokes.lean",
  "target": "hausdorff_measure_finite_on_compact",
  "hint": "Use MeasureTheory.Hausdorff.finite_of_isCompact",
  "forbidden": ["sorry", "trivial", "True", "admit"],
  "timeout_minutes": 30
}
```

Agents work in parallel, I merge results.

---

## Current Pillar Status

Let me assess each pillar's tractability:

### P1: Stokes (`Hodge/Deep/Pillars/Stokes.lean`)
- **Size**: ~200 lines
- **Sorries**: 5-8 estimated
- **Tractability**: MEDIUM (needs Hausdorff measure from Mathlib)
- **Key blocker**: `formEvalPairing` needs real implementation

### P2: Federer-Fleming (`Hodge/Deep/Pillars/FedererFleming.lean`)
- **Size**: ~150 lines
- **Sorries**: 3-5 estimated
- **Tractability**: HARD (flat norm compactness is deep GMT)
- **Key blocker**: Needs real `FlatNorm` definition

### P3: Harvey-Lawson (`Hodge/Deep/Pillars/HarveyLawson.lean`)
- **Size**: ~120 lines
- **Sorries**: 3-4 estimated
- **Tractability**: HARD (calibrated geometry → analytic varieties)
- **Key blocker**: Needs `IsAnalyticSet` to be real

### P4: GAGA (`Hodge/Deep/Pillars/GAGA.lean`)
- **Size**: ~150 lines
- **Sorries**: 3-5 estimated
- **Tractability**: VERY HARD (Chow's theorem is major algebraic geometry)
- **Key blocker**: Needs scheme/variety infrastructure from Mathlib

### P5: Microstructure (`Hodge/Deep/Pillars/Microstructure.lean`)
- **Size**: ~350 lines
- **Sorries**: 8-12 estimated
- **Tractability**: MEDIUM (combinatorial + analysis)
- **Key blocker**: Sheet construction, gluing estimates

---

## Recommended Execution Order

Based on dependencies and tractability:

### Wave 1 (Immediately Parallelizable)
1. **Stokes** - Has most Mathlib support
2. **FlatNorm basics** in `Hodge/Analytic/FlatNorm.lean`
3. **Template/Transport lemmas** in `Hodge/GMT/`

### Wave 2 (After Wave 1)
4. **Federer-Fleming** compactness (uses flat norm from Wave 1)
5. **Microstructure** gluing (uses template lemmas from Wave 1)

### Wave 3 (Deep Algebraic Geometry)
6. **Harvey-Lawson** (hard, needs research)
7. **GAGA** (very hard, may need Mathlib contributions)

### Wave 4 (Final Assembly)
8. **Integration** across all pillars
9. **Remove `.universal` stubs** from main proof
10. **Verify full pipeline**

---

## Agent Task Queue (Ready to Deploy)

### Task 1: `flatNorm_sum_le_sum_flatNorm`
```
File: Hodge/Analytic/FlatNorm.lean
Goal: Prove flatNorm (∑ i in s, T i) ≤ ∑ i in s, flatNorm (T i)
Hint: Finset.induction_on + flatNorm_add_le
Difficulty: EASY
```

### Task 2: `finSum_eq_sum_univ`
```
File: Hodge/Analytic/FlatNorm.lean
Goal: Prove finSum N T = ∑ i : Fin N, T i
Hint: Induction on N, use Finset.sum_univ_succ
Difficulty: EASY
```

### Task 3: `hausdorff_measure_finite_on_compact`
```
File: Hodge/Deep/Pillars/Stokes.lean
Goal: Prove μH[d] K < ⊤ for compact K
Hint: MeasureTheory.Hausdorff.finite_of_isCompact (check if in Mathlib)
Difficulty: MEDIUM
```

### Task 4: `realSubmanifoldIntegral_bound`
```
File: Hodge/Deep/Pillars/Stokes.lean
Goal: Complete the proof using MeasureTheory.integral_mono_of_nonneg
Hint: Need bound on ‖ω‖ * μ(S)
Difficulty: MEDIUM
```

### Task 5: `calibrated_current_analytic`
```
File: Hodge/Deep/Pillars/HarveyLawson.lean
Goal: Prove calibrated integral current has analytic support
Hint: This is deep - may need placeholder with documented blocker
Difficulty: HARD
```

---

## Verification Commands (All Agents)

```bash
# BEFORE any work
cd /Users/jonathanwashburn/Projects/hodge
lake exe cache get

# AFTER each change
lake build Hodge.Deep.Pillars.Stokes  # (or relevant file)

# BEFORE submitting
./scripts/agents/verify_agent_work.sh
lake env lean Hodge/Utils/DependencyCheck.lean
```

---

## What I Need From You

1. **Approval** to start direct work on the most tractable tasks
2. **Clarification** on priority:
   - Speed (do easiest first) vs
   - Impact (do most important first) vs
   - Depth (fully solve one pillar before moving)
3. **Resource allocation**: How many parallel agents/sessions to use?

---

## My Recommendation

**Start with Direct Work on Wave 1** (I do it myself):
- Tasks 1-2: FlatNorm lemmas (easy wins)
- Tasks 3-4: Stokes basics (tractable with Mathlib)

Then deploy 3-5 parallel agents on Wave 2 while I integrate Wave 1 results.

This hybrid approach (direct + orchestrated) should be fastest.
