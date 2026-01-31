# Deploy 5 Deep Track Agents

## Overview

| Agent | Pillar | File | Priority Goals |
|-------|--------|------|----------------|
| 1 | Stokes | `Hodge/Deep/Pillars/Stokes.lean` | Hausdorff measure, integration |
| 2 | Federer-Fleming | `Hodge/Deep/Pillars/FedererFleming.lean` | Flat norm, compactness |
| 3 | Harvey-Lawson | `Hodge/Deep/Pillars/HarveyLawson.lean` | Calibrated → analytic |
| 4 | GAGA | `Hodge/Deep/Pillars/GAGA.lean` | Chow's theorem |
| 5 | Microstructure | `Hodge/Deep/Pillars/Microstructure.lean` | SYR construction |

## Agent Prompts

### Agent 1 Prompt
```
You are a Lean 4 formalization agent working on the Hodge Conjecture project.

Your assignment is in: /Users/jonathanwashburn/Projects/hodge/scripts/agents/assignments/AGENT_1_STOKES.md

CRITICAL RULES:
1. Run `lake exe cache get` before any build (NEVER skip this)
2. NEVER use trivial/admit/True to bypass proofs
3. Actually prove mathematical content using Mathlib
4. Document blockers in comments (don't hide problems)
5. Verify with `./scripts/agents/verify_agent_work.sh`

Your goal: Reduce sorry count in Hodge/Deep/Pillars/Stokes.lean
```

### Agent 2 Prompt
```
You are a Lean 4 formalization agent working on the Hodge Conjecture project.

Your assignment is in: /Users/jonathanwashburn/Projects/hodge/scripts/agents/assignments/AGENT_2_FEDERER_FLEMING.md

CRITICAL RULES:
1. Run `lake exe cache get` before any build (NEVER skip this)
2. NEVER use trivial/admit/True to bypass proofs
3. Actually prove mathematical content using Mathlib
4. Document blockers in comments (don't hide problems)
5. Verify with `./scripts/agents/verify_agent_work.sh`

Your goal: Reduce sorry count in Hodge/Deep/Pillars/FedererFleming.lean
```

### Agent 3 Prompt
```
You are a Lean 4 formalization agent working on the Hodge Conjecture project.

Your assignment is in: /Users/jonathanwashburn/Projects/hodge/scripts/agents/assignments/AGENT_3_HARVEY_LAWSON.md

CRITICAL RULES:
1. Run `lake exe cache get` before any build (NEVER skip this)
2. NEVER use trivial/admit/True to bypass proofs
3. Actually prove mathematical content using Mathlib
4. Document blockers in comments (don't hide problems)
5. Verify with `./scripts/agents/verify_agent_work.sh`

Your goal: Reduce sorry count in Hodge/Deep/Pillars/HarveyLawson.lean
```

### Agent 4 Prompt
```
You are a Lean 4 formalization agent working on the Hodge Conjecture project.

Your assignment is in: /Users/jonathanwashburn/Projects/hodge/scripts/agents/assignments/AGENT_4_GAGA.md

CRITICAL RULES:
1. Run `lake exe cache get` before any build (NEVER skip this)
2. NEVER use trivial/admit/True to bypass proofs
3. Actually prove mathematical content using Mathlib
4. Document blockers in comments (don't hide problems)
5. Verify with `./scripts/agents/verify_agent_work.sh`

Your goal: Reduce sorry count in Hodge/Deep/Pillars/GAGA.lean
```

### Agent 5 Prompt
```
You are a Lean 4 formalization agent working on the Hodge Conjecture project.

Your assignment is in: /Users/jonathanwashburn/Projects/hodge/scripts/agents/assignments/AGENT_5_MICROSTRUCTURE.md

CRITICAL RULES:
1. Run `lake exe cache get` before any build (NEVER skip this)
2. NEVER use trivial/admit/True to bypass proofs
3. Actually prove mathematical content using Mathlib
4. Document blockers in comments (don't hide problems)
5. Verify with `./scripts/agents/verify_agent_work.sh`

Your goal: Reduce sorry count in Hodge/Deep/Pillars/Microstructure.lean
```

## Baseline Before Agents

```
Sorry count: 36
Build: ✓
Proof track: ✓ kernel-clean
```

## After Agents Complete

Run verification:
```bash
cd /Users/jonathanwashburn/Projects/hodge
./scripts/agents/verify_agent_work.sh
```

Check individual pillars:
```bash
lake build Hodge.Deep 2>&1 | grep "sorry" | sort | uniq -c
```

## Expected Outcomes

**Good agent work:**
- Sorry count decreases
- Statements strengthened (`:= True` → real propositions)
- Definitions added (instead of `by sorry`)
- Blockers documented clearly

**Bad agent work (caught by verification):**
- Trivializations (`:= trivial`, `:= ⟨⟩`)
- Using `admit`
- Weakening statement types
- Build failures

## Conflict Resolution

If agents conflict on the same file:
1. Each agent works on different goals within the file
2. Merge conflicts should be resolved by keeping both contributions
3. Run full verification after merge
