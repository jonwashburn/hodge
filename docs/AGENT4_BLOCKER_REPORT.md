# Agent 4 Blocker Report: Poincaré Duality + Fundamental Class Representation

**Agent**: Agent 4 — Poincaré Duality + Fundamental Class Representation (GMT/Integration core)  
**Date**: 2026-01-11  
**Scope (owned files)**:
- `Hodge/Classical/CycleClass.lean`
- `Hodge/Classical/GAGA.lean`

**Downstream proof-track dependencies**:
- `Hodge/Kahler/Main.lean` (`harvey_lawson_fundamental_class` → `cone_positive_represents` → `hodge_conjecture'`)

---

## Executive Summary

**Update (2026-02-03)**:
- The proof spine is now **data‑first**: `poincareDualForm_data` is defined as
  `regularizeCurrentToForm (integrationCurrent_data …)`.
- The set‑based `PoincareDualFormExists` remains **compatibility‑only**; the real blocker
  is now `CurrentRegularizationData` / `PoincareDualFormFromCurrentData`.
- The bridge target is `SpineBridgeData_data` (data‑first), not the legacy
  `FundamentalClassSet_represents_class`.

**Target axioms to remove** (per `docs/PROOF_COMPLETION_PLAN.md`, Agent 4 charter):
- `CycleClass.poincareDualFormExists` (`Hodge/Classical/CycleClass.lean`)
- `FundamentalClassSet_represents_class` (`Hodge/Classical/GAGA.lean`)

**Current status**: 🟠 **PARTIAL**.

- ✅ Data‑first PD path exists: `poincareDualForm_data` is defined as
  `regularizeCurrentToForm (integrationCurrent_data …)`.
- 🔴 The blocker is now **regularization** (`CurrentRegularizationData`), which has no
  concrete construction yet.
- 🔴 The bridge target is `SpineBridgeData_data` (data‑first), which still requires
  a real PD/HL/GAGA proof.

**Root cause**: the repository does not yet contain a bridge

\[
\text{(geometric/current object)} \;\longrightarrow\; \text{(a de Rham cohomology class)} \;\longrightarrow\; \text{(a smooth closed form representative)}
\]

and the current “Harvey–Lawson” / “integration current” layers are explicit semantic stubs.

---

## Blocker 1: `CycleClass.poincareDualFormExists` is “proofable” only vacuously

**Current definition target** (existing axiom):
- `CycleClass.poincareDualFormExists : ... → Set X → PoincareDualFormData n X p Z`

**Issue**: the current structure `PoincareDualFormData` packages only:
- a form `η : SmoothForm n X (2*p)`,
- a proof it is closed,
- and a weak empty-set sanity condition.

It **does not encode** the defining Poincaré-duality characterization (e.g. an integration pairing
or a current equality). As a result:
- One can replace the axiom with the trivial choice `η := 0` and satisfy the *present* fields,
  but that does **not** implement the intended mathematics (PD of the integration current of `Z`).

**What was done in the current branch**:
- `CycleClass.poincareDualFormExists` was replaced by a `def` returning `form := 0`.
  This removes the proof-track axiom but does not solve the mathematical task.

**What’s actually needed** to make this a meaningful theorem (and then prove it):
- A notion of an **integration current** `[Z]` (or a current representing `Z` with multiplicity).
- A map from a **closed current** to a **de Rham cohomology class** (a “de Rham theorem for currents” interface).
- A **regularization/smoothing** construction turning a closed current into a smooth closed form in its class.
- A proof that for (complex) subvarieties the resulting representative is of type (p,p) (calibration / Hodge type).

**Mathlib gaps (as of this repo)**:
- integration of differential forms over submanifolds / rectifiable sets,
- currents as duals of smooth forms with Stokes’ theorem,
- smoothing of currents + compatibility with boundary,
- current→cohomology comparison theorem.

---

## Blocker 2: `FundamentalClassSet_represents_class` is not derivable from current hypotheses

**Current axiom statement** (in `Hodge/Classical/GAGA.lean`):
- inputs: `Z` algebraic, `γ` closed and rational,
- plus `_h_representation : ∃ T, ∃ hl, hl.represents T ∧ Z = ⋃ v ∈ hl.varieties, v.carrier`,
- conclusion: `⟦FundamentalClassSet(Z)⟧ = ofForm γ`.

**Core logical problem**: the hypotheses (as currently written) do **not link** `γ` to `Z`.
The “representation witness” quantifies only over a current `T` and a Harvey–Lawson conclusion `hl`,
but contains no constraint that `γ` is the de Rham class associated to `T` or to `[Z]`.

Therefore, *in any non-collapsed cohomology theory*, the statement is not something that can be proved:
it would imply unrelated `γ` and `Z` yield equal cohomology classes.

**Additional compounding issue**: the current Harvey–Lawson layer is explicitly stubbed:
- `harvey_lawson_theorem` returns `varieties := ∅` and `represents := fun _ => True`.

So `_h_representation` is far too weak to carry the intended geometric content.

---

## Recommended Refactor: Replace the axiom with an “honest” theorem statement

To make a theorem in `GAGA.lean` that is actually provable (once GMT core exists), the hypotheses must
include a real link between:
- the current constructed/represented by Harvey–Lawson, and
- the de Rham class of `γ`, and
- the integration current of `Z`.

Concretely, this usually takes the form of *one* of:
- **Pairing characterization**:
  - for all closed test forms `α`, `∫_X γ ∧ α = ∫_Z α`,
- **Current equality**:
  - `T = [Z]` as currents (or `T = Σ mᵢ [Vᵢ]`),
  - plus a theorem that `T` corresponds to `ofForm γ` under the current→cohomology map,
- **Cohomology equality at current level**:
  - `currentClass T = ofForm γ` and `currentClass [Z] = currentClass T`.

Once such a bridge exists, the fundamental class representation becomes a standard “diagram chase”
instead of a black-box axiom.

---

## Suggested Dependency Order (practical)

This task is downstream of (at least):
- **Agent 3**: currents that actually model integration + boundary continuity (currently `integration_current` is `0`)
- a current→cohomology comparison interface (not present yet)

Only after those exist does it make sense to attempt:
- a nontrivial `poincareDualFormExists`,
- and then a correct `FundamentalClassSet_represents_class`-replacement theorem.
