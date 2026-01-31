# Agent 4: GAGA Pillar

## Setup (REQUIRED FIRST)
```bash
cd /Users/jonathanwashburn/Projects/hodge
lake exe cache get
```

## Your Target
**File**: `Hodge/Deep/Pillars/GAGA.lean`

## Context
Read `scripts/agents/AGENT_CONTEXT.md` for project rules.

## Current State
This file contains GAGA/Chow theorem formalization. Key goals:
1. `isAnalyticSetZeroLocus_implies_isAnalyticSet` - ✅ DONE
2. `isAnalyticSet_implies_isAnalyticSetZeroLocus` - hard (Cartan's theorem)
3. `IsAlgebraicSetStrong` - needs polynomial zero locus definition
4. `chow_theorem_strong` - Chow's theorem (analytic = algebraic on projective)
5. `ChowGAGAData.real` - the real instance

## Priority Tasks
1. **Strengthen `IsAlgebraicSetStrong`**:
   - Add proper polynomial zero locus field (not just `True`)
   - Reference: homogeneous polynomials in projective embedding

2. **Work toward `chow_theorem_strong`**:
   - This is research-level, but you can:
   - Add helper lemmas
   - Document the proof structure from Chow 1949

3. **Explore what Mathlib has**:
   - `AlgebraicGeometry.ProjectiveSpectrum`
   - `Geometry.Manifold.Complex`

## Mathematical Background
- Chow 1949: "On compact complex analytic varieties"
- Serre 1956: GAGA
- Key: Closed analytic subset of ℙⁿ is algebraic

## ⚠️ RULES
- NEVER use `trivial`, `admit`, `:= True`, `:= ⟨⟩`
- Actually prove using Mathlib lemmas
- Document blockers in comments if stuck
- Run `lake build Hodge.Deep.Pillars.GAGA` after each change

## Verification
```bash
./scripts/agents/verify_agent_work.sh
```

## Success = sorry count decreases OR statements strengthened OR real definitions added
