# Agent 3: Harvey-Lawson Pillar

## Setup (REQUIRED FIRST)
```bash
cd /Users/jonathanwashburn/Projects/hodge
lake exe cache get
```

## Your Target
**File**: `Hodge/Deep/Pillars/HarveyLawson.lean`

## Context
Read `scripts/agents/AGENT_CONTEXT.md` for project rules.

## Current State
This file contains calibrated geometry theorems. Key goals:
1. `harvey_lawson_decomposition` - calibrated currents decompose into analytic varieties
2. `calibrated_current_is_cycle` - calibrated ⟹ cycle (boundary = 0)
3. `support_is_analytic_variety` - support of calibrated current is analytic
4. `decomposition_represents_current` - the decomposition sums to original

## Priority Tasks
1. **Prove `calibrated_current_is_cycle`**:
   - Use: calibration ⟹ ∂T = 0 (calibrated currents are closed)
   - Key insight: if T is calibrated by ω, then mass(T) = T(ω), so any boundary would increase mass
   
2. **Structure `harvey_lawson_decomposition`**:
   - Input: T calibrated by Kähler form
   - Output: finite sum of integration currents over analytic subvarieties

## Mathematical Background
- Harvey-Lawson 1982: "Calibrated Geometries"
- Key theorem: Calibrated integral currents in Kähler manifolds are sums of complex subvarieties

## ⚠️ RULES
- NEVER use `trivial`, `admit`, `:= True`, `:= ⟨⟩`
- Actually prove using Mathlib lemmas
- Document blockers in comments if stuck
- Run `lake build Hodge.Deep.Pillars.HarveyLawson` after each change

## Verification
```bash
./scripts/agents/verify_agent_work.sh
```

## Success = sorry count decreases OR statements strengthened OR real definitions added
