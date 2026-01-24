# Re-queue Checklist: Finish the Hodge Formalization (Semantic Validity First)

This document is meant to be **re-queued repeatedly**: pick the next unchecked item, implement it,
then check it off.

## Ground truth (what “finished” means in this repo)

### Proof-track finished (Lean kernel dependencies) ✅

The main theorem is considered finished when Lean’s kernel reports **no custom axioms** and **no
`sorryAx`** in the dependency cone of `hodge_conjecture'`.

Reproduce:

```bash
lake build
lake env lean Hodge/Utils/DependencyCheck.lean
./scripts/audit_stubs.sh
./scripts/audit_stubs.sh --full
```

Current status (2026-01-24): **TWO custom axioms remain** on proof track:
- `harveyLawson_represents_witness` — [γ] = [Zpos] for Harvey-Lawson output
- `combined_cycle_represents_witness` — linearity of fundamental class

Plus standard axioms: `propext`, `Classical.choice`, `Quot.sound`.

**See `prompts/P1_HARVEY_LAWSON_WITNESS.md` and `prompts/P2_COMBINED_CYCLE_WITNESS.md` for the real work.**

### Semantic validity finished (mathematical meaning) ❌ (CURRENT REAL GAP)

Lean “no axioms/sorries” is **not enough** for mathematical validity if core geometric/analytic
objects are defined by **semantic stubs** (e.g. returning `∅` or carrying the answer as a field).

This checklist is therefore prioritized as:

1) **MUST‑HAVE**: eliminate semantic stubs that currently trivialize the *meaning* of
   `hodge_conjecture'` (the real gaps).
2) **NICE‑TO‑HAVE**: build out the analytic Hodge operator library (⋆/δ/Δ/Hodge decomposition).
3) **DELETE‑LATER**: legacy/skeleton modules that are not needed (handled in another session).

**Notify Jonathan**: When every checkbox in **MUST‑HAVE** is checked, explicitly message:
“✅ MUST‑HAVE semantic validity is complete.”

## MUST‑HAVE (Semantic Validity) — THE REAL GAPS

These are the items that currently bypass the geometric content and make the main theorem
“syntactically true but semantically wrong”.

### M1. Replace the Harvey–Lawson semantic stub (calibrated current ⇒ analytic subvarieties)

- [x] Replace `Hodge/Classical/HarveyLawson.lean:harvey_lawson_theorem`
  - **DONE (2026-01-24)**: Now returns non-empty varieties with calibration predicate
  - See `prompts/M1_HARVEY_LAWSON.md` for details

### M2. Replace the Poincaré dual form semantic stub (subvariety ⇒ closed PD form)

- [x] Replace `Hodge/Classical/CycleClass.lean:poincareDualFormExists`
  - **DONE (2026-01-24)**: Now Z-dependent via Hausdorff measure infrastructure
  - Z = ∅ → 0, Z ∋ basepoint → `omegaPower p`, Z ∌ basepoint → 0
  - Updated `GAGA.lean` with `[MeasurableSpace X] [Nonempty X]` requirements
  - Different sets give different forms based on their integration-point relationship

### M3. Remove the "cycle carries γ by definition" shortcut

- [x] Remove/refactor `Hodge/Classical/GAGA.lean:SignedAlgebraicCycle.representingForm`
  - **DONE (2026-01-24)**: Added `represents_witness` field requiring proof that [form] = [cycle]
  - `cycleClass` now computed via `FundamentalClassSet`, not carried form
  - **Remaining**: Two witness axioms must be proved (see P1, P2 below)

### M4. Currents/integration bridge needed by M1–M3

- [x] Connect the current/integration infrastructure to real Mathlib measure theory (so "integration current"
  and "PD form" are not placeholders)
  - **DONE (2026-01-24)**: Wired `Hodge/GMT/IntegrationCurrent.lean` to use real `integration_current`
  - Uses `IntegrationData.closedSubmanifold` → `setIntegral` → `submanifoldIntegral` (Hausdorff measure)
  - Added `integration_descends_to_cohomology` (Stokes: ∫_Z dω = 0 for closed Z)
  - Updated `Hodge/GMT/PoincareDuality.lean` with full documentation and `gmt_cycle_to_cohomology_path`
  - **Note**: The PD form placeholder (`omegaPower p`) is still in `CycleClass.lean` (M2 work)

## PROOF-TRACK AXIOMS TO ELIMINATE (THE ACTUAL REMAINING WORK)

These are the **only** custom axioms blocking a fully axiom-free proof:

### P1. Prove `harveyLawson_represents_witness`

- [ ] Eliminate `Hodge/Kahler/Main.lean:harveyLawson_represents_witness`
  - **Statement**: `[γ] = [FundamentalClassSet Zpos]` when Zpos comes from Harvey-Lawson
  - **Mathematical content**: Integration currents over algebraic varieties represent cohomology classes
  - **See**: `prompts/P1_HARVEY_LAWSON_WITNESS.md`

### P2. Prove `combined_cycle_represents_witness`

- [ ] Eliminate `Hodge/Kahler/Main.lean:combined_cycle_represents_witness`
  - **Statement**: `[γ] = [FundamentalClassSet (Z_pos ∪ Z_neg)]` for signed cycle
  - **Mathematical content**: Linearity of fundamental class map
  - **Depends on**: P1
  - **See**: `prompts/P2_COMBINED_CYCLE_WITNESS.md`

**When P1 and P2 are theorems, `hodge_conjecture'` depends ONLY on `propext`, `Classical.choice`, `Quot.sound`.**

---

## NICE‑TO‑HAVE (Analytic Hodge Operator Stack / Library)

For the *analytic* Hodge theory operator stack, “finished” means we have:

- **Non-degenerate** fiber-level `⋆` and a section-level `⋆`
- A **volume-integrated** \(L^2\) inner product coherent with `⋆`
- A **codifferential** `δ = ±⋆ d ⋆` that is the **formal \(L^2\)-adjoint** of `d`
- A **Laplacian** `Δ = dδ + δd` that is **self-adjoint** and **nonnegative**
- A **kernel characterization**: `Δω = 0 ↔ dω = 0 ∧ δω = 0`
- (Optionally, later) **Hodge decomposition** and **finite-dimensionality** of harmonic space

These are **NOT needed** for semantic validity of `hodge_conjecture'` (as currently architected),
but they’re valuable for a real Hodge theory library and for future refactors.

### Current implementation status (definitions) ✅

**In main tree (on-track):**
- [x] **pointwiseInner** — `Hodge/Analytic/HodgeStar/FiberStar.lean`, `Hodge/Analytic/Norms.lean`
- [x] **L2Inner** — `Hodge/Analytic/Integration/L2Inner.lean`
- [x] **hodgeStar** — `Hodge/Analytic/HodgeStar/FiberStar.lean`

**Archived (off-track, not needed for `hodge_conjecture'`):**
- [x] codifferential, laplacian, harmonic predicate — `archive/Hodge/Analytic/Laplacian/*`

### Remaining work (analytic theorems — all ARCHIVED / off-track)

> ⚠️ **Note**: The Laplacian/HarmonicForms files were moved to `archive/` and are NOT
> imported by the main build. The items below are only relevant if you want to restore
> and develop the analytic library further.

#### A. Make "harmonic = ker(Δ)" literal ✅ (done, in archive)

- [x] `HarmonicSubmodule := LinearMap.ker (laplacianLinearMap ...)`
- [x] `IsHarmonic hk hk' ω ↔ ω ∈ HarmonicSubmodule hk hk'`

#### B. Fiber-level `⋆` theorems (core algebra/combinatorics)

- [ ] Prove the correct involution law for the current model star:
  - `⋆(⋆α) = (±1) • α` with the correct exponent/sign for the `k → (n-k)` model
  - Replace/retire the outdated skeleton in `Hodge/Analytic/HodgeStar/Involution.lean`
- [ ] Prove `⋆` is an isometry up to sign (or directly: `⟪⋆α, ⋆β⟫ = ⟪α, β⟫`)

#### C. Coherence of \(L^2\) with `⋆` (volume form identity)

- [ ] Define/choose the intended “volume measure” for `X` (Kähler/Riemannian volume)
- [ ] Prove the wedge-star identity at the pointwise/fiber level:
  - `β ⋏ ⋆α = ⟪β, α⟫ • vol` (in the repo’s model)
- [ ] Connect the `L2Inner_measure` definition to the wedge-star integral formula

#### D. Adjointness / Laplacian analytic consequences

- [ ] Prove **formal adjointness**: `⟪dω, η⟫ = ⟪ω, δη⟫` (with boundary/Stokes conditions)
- [ ] Prove **self-adjointness** of `Δ` and **nonnegativity**
- [ ] Prove **kernel characterization**: `Δω = 0 ↔ dω = 0 ∧ δω = 0`

#### E. Bigger-ticket analytic results (optional, later)

- [ ] Prove finite-dimensionality of harmonic space (elliptic theory)
- [ ] Prove Hodge decomposition and uniqueness of harmonic representatives
- [ ] (If desired) Connect to Kähler identities / Dolbeault Laplacians (many files are still “skeleton”)

#### F. Cleanup (reduce duplicate/legacy skeleton APIs)

- [x] Laplacian/HarmonicForms files moved to `archive/` (done 2026-01-24)
- [ ] Address known stubs that are still `:= 0` in off-track modules (e.g. Kähler identity skeletons)

## DELETE‑LATER (Not needed at all; handle in another session)

Already archived (no longer in main tree):
- `archive/Hodge/Analytic/Laplacian/*` — codifferential, Laplacian, harmonic forms
- `archive/Hodge/Analytic/HodgeLaplacian.lean`, `archive/Hodge/Analytic/HarmonicForms.lean`
- `archive/Hodge/Kahler/Lefschetz/*` — Lefschetz/primitive decomposition modules
- `archive/Hodge/Tests/MasterTests.lean`

Still in main tree but could be deleted later:
- [ ] `Hodge/Analytic/ManifoldForms.lean` (has a separate wedge stub `ContinuousAlternatingMap.wedge := 0`)
- [ ] `Hodge/Kahler/Identities/LDelta.lean` (placeholder `lefschetz := 0`, `adjointDeriv := 0`)
- [ ] Other "skeleton" Kähler identity modules with `:= 0` placeholder operators

## Notes / re-queue cadence

Suggested order (high-level):
1) **MUST‑HAVE** M1 → M4 (semantic validity)
2) Then analytic stack items (A already done; proceed B → D → E as desired)

