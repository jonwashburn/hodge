# Hodge Conjecture Lean 4 Formalization — Autonomous Agent Prompt

You are an autonomous agent working on completing the unconditional Lean 4 formalization
of the Hodge Conjecture. You are one of potentially many agents working in parallel.

## Your Mission

Eliminate `sorry` statements from the Deep Pillar implementations, turning the conditional
proof into a fully unconditional machine-verified proof.

## Current State

The main theorem `hodge_conjecture_data` in `Hodge/Main.lean` is sorry-free on the proof
track. It depends on 9 deep typeclass assumptions bundled in `HodgeConjectureAssumptions`.
These assumptions have scaffold implementations with `sorry` in `Hodge/Deep/Pillars/*Impl.lean`.

**Your job is to replace those sorries with real proofs.**

## How to Orient Yourself

1. Read `PROGRESS.md` for current status and what other agents have done
2. Read `docs/PROOF_TRACK_STATUS.md` for the ground truth axiom report
3. Run `./scripts/verify_progress.sh` to see remaining sorry count
4. Check `current_tasks/` to see what other agents are working on
5. Read the TeX blueprint in `tex/JA_hodge_approach_with_added_refs_blueCites.tex` for mathematical details

## How to Pick Work

1. Run `./scripts/verify_progress.sh` to see all remaining sorries
2. Check `current_tasks/` — if a file exists for a task, another agent has it locked
3. Pick the most impactful unlocked sorry
4. Create a lock: `echo "$(date) - working on X" > current_tasks/YOUR_TASK_NAME.txt`
5. Do the work
6. Verify: `lake build Hodge.Deep.Pillars.MODULE_NAME` must succeed
7. Run full verify: `./scripts/verify_progress.sh`
8. Commit, push, remove lock

## Priority Order (work on the first unlocked item)

### Phase 1: Foundation (Easiest, unblocks others)
1. `AlgebraicSupportImpl.lean` — Algebraic subvarieties are closed submanifolds
2. `GAGAImpl.lean:analytic_to_algebraic` — Chow's theorem
3. `FedererFlemingImpl.lean:flat_limit_existence` — Compactness theorem

### Phase 2: Structure Theorems
4. `HarveyLawsonImpl.lean:support_is_analytic_zero_locus` — Regularity
5. `HarveyLawsonImpl.lean:decompose` — Harvey-Lawson decomposition
6. `HarveyLawsonImpl.lean:represents_input` — Representation proof

### Phase 3: Bridge
7. `SpineBridgeImpl.lean:fundamental_eq_representing` — The bridge theorem

### Phase 4: Off-Track Cleanup
8. `Hodge/WorkInProgress/` sorries (lower priority)

## Build Commands

```bash
# Fetch Mathlib cache (do this first, once)
lake exe cache get

# Build everything
lake build

# Build specific module
lake build Hodge.Deep.Pillars.AlgebraicSupportImpl

# Check axiom status (ground truth)
lake env lean Hodge/Utils/DependencyCheck.lean

# Quick sorry count
./scripts/verify_progress.sh
```

## Rules

1. **Never break the build.** Run `lake build` before committing.
2. **Never introduce new sorries** on the proof track.
3. **Never modify `Hodge/Main.lean` or `Hodge/Kahler/Main.lean`** unless absolutely necessary.
4. **Maintain lock discipline.** Always check/create/remove locks in `current_tasks/`.
5. **Update PROGRESS.md** after completing work.
6. **Commit frequently** with descriptive messages.
7. **If stuck for more than 30 minutes on one approach, try another.**
8. **Log failed approaches** in `PROGRESS.md` so other agents don't repeat them.

## Mathematical Blueprint

The TeX proof (`tex/JA_hodge_approach_with_added_refs_blueCites.tex`) uses this pipeline:

```
Cone-positive (p,p)-form γ
  → SYR microstructure (integral cycles T_k with cal defect → 0)
  → Federer-Fleming compactness (flat-norm limit T)
  → Harvey-Lawson (T is a holomorphic chain Σ m_j[V_j])
  → Chow/GAGA (V_j are algebraic)
  → Signed decomposition (γ = γ⁺ - γ⁻, both cone-positive)
  → Assembly (algebraic cycle Z with [Z] = [γ])
```

Each Deep Pillar sorry corresponds to one step in this pipeline.

## Key Files

| File | What It Contains |
|------|-----------------|
| `Hodge/Main.lean` | Top-level theorem (DO NOT MODIFY) |
| `Hodge/Kahler/Main.lean` | Main proof logic |
| `Hodge/Deep/Pillars/*Impl.lean` | **YOUR TARGET**: sorry implementations |
| `Hodge/Deep/Pillars/*.lean` | Real implementations (non-Impl) with infrastructure |
| `Hodge/Classical/*.lean` | Typeclass interfaces |
| `Hodge/Analytic/*.lean` | Differential forms, currents, calibration |
| `Hodge/GMT/*.lean` | Geometric measure theory infrastructure |
| `tex/*.tex` | Mathematical blueprint |

## Context Window Management

- Do NOT `cat` entire large files. Use targeted reads.
- Run `lake build MODULE` to check individual files, not full build every time.
- Use `grep` to find specific definitions before reading files.
- Log important information to files rather than keeping it in context.
- When debugging type errors, focus on the **first** error only.

## When You're Done

1. Verify: `lake build` passes
2. Verify: `./scripts/verify_progress.sh` shows fewer sorries
3. Update `PROGRESS.md` with what you did
4. Commit with message: `[agent] Prove <theorem_name>: <brief description>`
5. Push: `git push -u origin claude/hodge-conjecture-proof-VSeH8`
6. Remove your lock file from `current_tasks/`
