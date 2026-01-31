# Agent 5: Microstructure Pillar

## Setup (REQUIRED FIRST)
```bash
cd /Users/jonathanwashburn/Projects/hodge
lake exe cache get
```

## Your Target
**File**: `Hodge/Deep/Pillars/Microstructure.lean`

## Context
Read `scripts/agents/AGENT_CONTEXT.md` for project rules.

## Current State
This file contains the SYR microstructure construction. Key goals:
1. `exists_cubulation_with_properties` - cubulation of compact manifold exists
2. `holomorphic_sheet_construction` - local holomorphic sheets from form zeros
3. `raw_sheet_sum_gluing_properties` - sheets glue correctly
4. `microstructure_sequence_properties` - the sequence Tₙ exists
5. `microstructure_defect_vanishes` - calibration defect → 0

## Priority Tasks
1. **Prove `exists_cubulation_with_properties`**:
   - Use: `IsCompact.exists_finite_cover`
   - Subdivide into coordinate cubes
   
2. **Structure `holomorphic_sheet_construction`**:
   - Input: ω ∈ H^{p,p} nonzero at point
   - Output: local complex submanifold where ω restricts nondegenerately

3. **Work toward `microstructure_defect_vanishes`**:
   - This is the key result connecting to the main theorem
   - Calibration defect = mass(T) - T(ω^p/p!) → 0 as mesh → 0

## Mathematical Background
- Siu-Yau-Ran construction
- Key: refine cubulation → sheets approximate → defect vanishes

## Mathlib Resources
- `IsCompact.exists_finite_cover`
- `TopologicalSpace.IsTopologicalBasis`
- `Filter.Tendsto` for mesh → 0

## ⚠️ RULES
- NEVER use `trivial`, `admit`, `:= True`, `:= ⟨⟩`
- Actually prove using Mathlib lemmas
- Document blockers in comments if stuck
- Run `lake build Hodge.Deep.Pillars.Microstructure` after each change

## Verification
```bash
./scripts/agents/verify_agent_work.sh
```

## Success = sorry count decreases OR statements strengthened OR real definitions added
