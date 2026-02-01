# Autonomous Agent Architecture for Full-Unconditional Completion

## Overview

This document describes a scalable architecture for completing the Hodge Conjecture formalization using autonomous agents managed by a coordinating AI (the "Integrator").

## Architecture Layers

```
┌──────────────────────────────────────────────────────────────────┐
│                     INTEGRATOR (Claude)                          │
│  - Coordinates all agents                                        │
│  - Merges work, resolves conflicts                               │
│  - Makes cross-cutting semantic decisions                        │
│  - Maintains kernel-clean status                                 │
└────────────────────────────────────────────────────────────────────┘
                              │
        ┌─────────────────────┼─────────────────────┐
        ▼                     ▼                     ▼
┌────────────────┐   ┌────────────────┐   ┌────────────────┐
│  PILLAR AGENTS │   │  INFRA AGENTS  │   │  LEMMA AGENTS  │
│  (5 parallel)  │   │  (3 parallel)  │   │  (N parallel)  │
└────────────────┘   └────────────────┘   └────────────────┘
        │                     │                     │
        ▼                     ▼                     ▼
┌──────────────────────────────────────────────────────────────────┐
│                        Hodge/ CODEBASE                           │
│  29,000 lines • Kernel-unconditional • ~70% semantic stubs       │
└──────────────────────────────────────────────────────────────────┘
```

---

## Agent Types

### 1. Pillar Agents (5 agents, 1 per deep theorem)

Each handles ONE of the 5 major mathematical pillars:

| Agent | Pillar | File | Mathematical Goal |
|-------|--------|------|-------------------|
| P1 | **Stokes** | `Hodge/Deep/Pillars/Stokes.lean` | Real Hausdorff integration + Stokes theorem |
| P2 | **Federer-Fleming** | `Hodge/Deep/Pillars/FedererFleming.lean` | Flat norm compactness + closure |
| P3 | **Harvey-Lawson** | `Hodge/Deep/Pillars/HarveyLawson.lean` | Calibrated currents → analytic varieties |
| P4 | **GAGA** | `Hodge/Deep/Pillars/GAGA.lean` | Chow's theorem (analytic → algebraic) |
| P5 | **Microstructure** | `Hodge/Deep/Pillars/Microstructure.lean` | SYR sheet construction + defect → 0 |

**Scope**: Each agent works ONLY on their assigned file. No cross-file edits.

**Constraint**: Must not introduce `:= 0`, `:= True`, `trivial`, `admit`, or `sorry`.

### 2. Infrastructure Agents (3 agents)

| Agent | Focus | Files | Goal |
|-------|-------|-------|------|
| I1 | **Forms/TestForms** | `Hodge/Analytic/TestForms/*.lean` | Real LF topology |
| I2 | **Integration** | `Hodge/Analytic/Integration/*.lean` | Real submanifold integration |
| I3 | **GMT Core** | `Hodge/GMT/*.lean` | Real current support, mass, flat norm |

### 3. Lemma Agents (N agents, dynamically spawned)

Small, single-task agents for specific lemmas:
- Prove a single lemma
- Add a helper definition
- Document a blocker

**Lifespan**: Complete one task, then terminate.

---

## Coordination Protocol

### Phase 1: Parallel Pillar Probing (Hours 0-4)

1. Deploy all 5 Pillar Agents simultaneously
2. Each agent:
   - Reads their assigned file
   - Identifies sorries/stubs
   - Attempts to prove OR documents blockers
3. Integrator collects results every 30 min

### Phase 2: Dependency-Aware Sequencing (Hours 4-12)

Based on Phase 1 results, sequence work by dependency:

```
M1 (TestForms) ─────┐
                    ├──► M3 (Current.support) ──► M7 (Cycle class)
M2 (Integration) ───┤                              │
                    ├──► M4 (IsAnalyticSet) ──────┘
M6 (Hodge ops) ─────┘         │
                              ▼
                    M5 (IsAlgebraicSet) ──► M8 (Microstructure)
                              │                    │
                              ▼                    ▼
                    M9 (Federer-Fleming) ──► M10 (Final assembly)
```

### Phase 3: Integration Sweeps (Hours 12-24)

1. Integrator merges all agent work
2. Runs full verification suite
3. Identifies remaining gaps
4. Spawns targeted Lemma Agents

---

## Scalability Mechanisms

### Horizontal Scaling

- **More Pillar Agents**: Can split pillars further (e.g., Stokes → StokesManifold + StokesBoundary)
- **More Lemma Agents**: Spawn 10-50 single-task agents for small lemmas
- **Parallel verification**: Run `lake build` on multiple files concurrently

### Vertical Scaling

- **Smarter Agents**: Use more capable models for harder pillars
- **Longer context**: Feed full file context for complex proofs
- **Better hints**: Accumulate proof patterns in `PROOF_HINTS.md`

---

## Verification Pipeline

Every agent change must pass:

```bash
# 1. Cache (mandatory)
lake exe cache get

# 2. Build
./scripts/build.sh

# 3. Kernel check
lake env lean Hodge/Utils/DependencyCheck.lean

# 4. Stub audit
./scripts/audit_stubs.sh --full

# 5. Gotcha check
./scripts/audit_practical_unconditional.sh
```

**Rejection criteria** (agent work is discarded):
- Any new `sorry`, `axiom`, `opaque`
- Any `:= trivial`, `:= True`, `:= ⟨⟩`
- Any `:= 0` for key operations
- Build failure

---

## Success Metrics

| Metric | Current | Target |
|--------|---------|--------|
| Sorries on proof track | 0 | 0 (maintain) |
| Custom axioms | 0 | 0 (maintain) |
| Semantic stubs | ~25 | 0 |
| `IsAnalyticSet := IsClosed` | Yes | No (real definition) |
| `SubmanifoldIntegration.integral := 0` | Yes | No (real integration) |
| `cycleClass_geom := cycleClass` | Yes | No (geometric definition) |

---

## Estimated Timeline (Aggressive)

| Phase | Duration | Parallelism | Expected Output |
|-------|----------|-------------|-----------------|
| P1: Pillar Probing | 4h | 5 agents | Blockers identified, easy lemmas proved |
| P2: Dependency Work | 8h | 8 agents | M1-M3 complete, M4-M6 started |
| P3: Integration | 12h | 3 agents + integrator | M4-M9 complete |
| P4: Final Assembly | 4h | Integrator only | M10 complete |

**Total**: ~28 hours of wall-clock time with full parallelism.

---

## Quick Start

### Option A: Deploy 5 Pillar Agents Now

```bash
cd /Users/jonathanwashburn/Projects/hodge

# Read the deployment guide
cat scripts/agents/DEPLOY_5_AGENTS.md

# Each agent gets their assignment file:
# scripts/agents/assignments/AGENT_1_STOKES.md
# scripts/agents/assignments/AGENT_2_FEDERER_FLEMING.md
# scripts/agents/assignments/AGENT_3_HARVEY_LAWSON.md
# scripts/agents/assignments/AGENT_4_GAGA.md
# scripts/agents/assignments/AGENT_5_MICROSTRUCTURE.md
```

### Option B: Have Integrator (Me) Manage Everything

I can:
1. Read all pillar files
2. Identify the most tractable lemmas
3. Prove them directly OR generate targeted agent tasks
4. Commit progress incrementally
5. Maintain kernel-clean status throughout

---

## Risk Mitigation

| Risk | Mitigation |
|------|------------|
| Agent introduces trivializations | Automated rejection via `FORBIDDEN_PATTERNS` |
| Agent breaks build | Rollback commit, re-run with more context |
| Agents conflict on same file | Each agent has exclusive file assignment |
| Mathlib lacks needed lemmas | Document in `docs/MATHLIB_GAPS.md`, build workaround |
| Proof is genuinely hard | Integrator takes over, uses TeX as guide |

---

## Next Steps

1. **Approve this architecture** (or modify)
2. **Deploy Phase 1** (5 Pillar Agents)
3. **Monitor progress** (I'll report every 30 min)
4. **Iterate** based on results
