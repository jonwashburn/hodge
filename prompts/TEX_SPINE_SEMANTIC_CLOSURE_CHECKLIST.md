# TeX Spine Semantic Closure Checklist (repeatable prompt)

This checklist is the **concrete, per-file implementation plan** to make the Lean development match the TeX spine:

> **SYR → glue-gap → realization-from-almost → Harvey–Lawson/King → Chow/GAGA → (only then) geometric `cycleClass`**

It is written to be used as a **repeatable prompt for an AI coding agent**: follow the steps in order, keep the repo building after every batch, and do not “paper over” missing math by redefining semantic objects.

---

## Guardrails (repo rules + workflow)

- **CRITICAL**: never rebuild Mathlib from source.
  - Before any `lake build`, run `lake exe cache get`.
  - Prefer `./scripts/build.sh` for builds.
- Keep the proof track compiling **at all times**. If a step is deep, introduce **new modules** and wire them in only when complete.
- Kernel dependency check is the ground truth:

```bash
./scripts/build.sh Hodge.Utils.DependencyCheck
lake env lean Hodge/Utils/DependencyCheck.lean
```

- When you introduce temporary assumptions, prefer **typeclass parameters** (assumptions) over global `axiom`s. Do **not** let them leak into `#print axioms hodge_conjecture'`.

---

## Strategy for staying buildable while replacing semantic stubs

### Two-track pattern (recommended)

For each semantic component (microstructure, HL/King, GAGA, cycleClass):

1. **Add** new “real” definitions/lemmas under a suffix/namespace (e.g. `_real`, `Hodge.TexSpine`).
2. Keep the current stubbed implementation used by `hodge_conjecture'` until the “real” replacement is ready.
3. Once the “real” component compiles and has the required theorems, **flip the proof-track wiring** in one PR.
4. Only then delete the stub code.

This keeps `hodge_conjecture'` compiling continuously while you develop the real spine.

---

## Step 1 — SYR (Automatic SYR) becomes real

### Goal (TeX)
Implement `thm:automatic-syr`: from a smooth closed cone-valued form β representing `[γ]`, construct a fixed-multiple SYR sequence of integral cycles with defect → 0.

### Files to change

#### `Hodge/Kahler/Microstructure.lean` (PRIMARY)

**Replace these explicit semantic stubs** (all currently “true because zero”):

- `topFormIntegral : SmoothForm n X (2 * n) → ℝ := fun _ => 0`
  - **Replace with** a real top-degree integral (likely via `Hodge/Analytic/Integration/VolumeForm.lean` / `integrateDegree2p` infrastructure).
- `VolumeIntegrationData`/`RawSheetSum.toIntegrationData` currently uses `integrate := fun _ => 0`
  - **Replace with** integration over the sheet geometry.
- `RawSheetSum.toCycleIntegralCurrent` returns `zeroCycleCurrent …`
  - **Replace with** the actual current corresponding to the sheet sum.
- `RawSheetSum.toIntegralCurrent_toFun_eq_zero`
  - **DELETE** once `toIntegralCurrent` is real.
- `microstructureSequence_is_zero`
  - **DELETE** once `microstructureSequence` is real.
- `RawSheetSum.current_is_zero`, `RawSheetSum.hasStokesProperty` (proved via zero)
  - **REPROVE** from the real construction, or replace by the correct bound interfaces.

**Minimal new interfaces to introduce (to keep proof track building)**:

- Add a new definition `RawSheetSum.toIntegralCurrent_real` and keep the existing `toIntegralCurrent` until ready.
- Add a lemma `RawSheetSum.toIntegralCurrent_eq_real` *only after* the real construction is implemented.
- Do NOT rewrite the proof-track entry points (`microstructureSequence`, `microstructureSequence_flat_limit_exists`, etc.) until the real current exists and has mass bounds.

#### `Hodge/Kahler/Main.lean`

This file already contains:
- `microstructure_construction_core`
- `microstructure_approximation`
- `automatic_syr`

**Checklist**:
- Ensure these theorems are stated in a way that does **not** depend on “zero current” artifacts.
- When you flip to the real microstructure, make sure:
  - the produced `T_seq` are actually cycles (`∂T_k = 0`), and
  - the calibration defect limit is the TeX-style one (not vacuous).

---

## Step 2 — glue-gap (microstructure/gluing estimate) becomes real

### Goal (TeX)
Implement `prop:glue-gap`: given raw current `T_raw`, fill boundary mismatch with controlled mass depending on the flat norm.

### Files to change

#### `Hodge/Kahler/Microstructure.lean` (PRIMARY)

**Replace these stubs**:

- `gluing_mass_bound` is currently proved by reducing to the zero current via `RawSheetSum.toIntegralCurrent_toFun_eq_zero`.
  - **Replace with** a proof using:
    - flat norm decomposition \(R = R_0 + ∂Q\),
    - an isoperimetric/filling lemma on `X`,
    - mass bounds compatible with TeX: `Mass(R_glue) ≤ δ + C δ^(k/(k−1))`.

#### `Hodge/GMT/FedererFleming.lean` (LIKELY)

Use this as the home for:
- isoperimetric inequality / filling lemma (via Nash embedding or existing Mathlib infrastructure),
- closure of integrality under pushforward, etc.

**Minimal interface to add**:

- A class/structure (temporary) like:
  - `IsoperimetricFillingData`: given an integral cycle `R₀`, returns an integral filling `Q₀` with mass exponent bound.
  - This can be assumed initially and later replaced with a proof.

---

## Step 3 — realization-from-almost (closure principle) matches TeX hypotheses

### Goal (TeX)
Implement `thm:realization-from-almost`: fixed-class, almost-calibrated cycles admit a calibrated limit cycle.

### Files to verify/extend

#### `Hodge/Analytic/Calibration.lean`

Already contains the core lemma:
- `limit_is_calibrated`

**Checklist**:
- Ensure you have (or add) the TeX-required ingredients:
  - evaluation continuity under flat norm (`eval_tendsto_of_flatNorm_tendsto`)
  - mass lower semicontinuity (`mass_lsc`)
  - `⟨T, ψ⟩ ≤ Mass(T)` from `comass(ψ) ≤ 1`

**Minimal missing interface to add**:
- A lemma specifically for the Kähler/Wirtinger calibration:
  - `comass (KählerCalibration …).form ≤ 1`

#### `Hodge/Classical/HarveyLawson.lean`

Already contains:
- `flat_limit_of_cycles_is_cycle`
- `calibrated_limit_is_cycle`

**Checklist**:
- Align the closure statement with TeX: cycle property, fixed class, and calibrated equality `Mass(T)=⟨T,ψ⟩`.

---

## Step 4 — Harvey–Lawson / King (calibrated ⇒ holomorphic chain) becomes real

### Goal (TeX)
Replace the semantic stub of the Harvey–Lawson structure theorem and King’s theorem.

### File to change

#### `Hodge/Classical/HarveyLawson.lean` (PRIMARY)

**Current stub indicators**:
- `harveyLawsonSupportVariety` has `carrier := Set.univ`
- `harvey_lawson_theorem` returns `varieties := {Set.univ}`
- `represents := fun T => isCalibrated T hyp.ψ` (predicate only; no decomposition)

**Replace with**:
- A theorem/data producing:
  - finitely many analytic subvarieties `V_j`,
  - multiplicities `m_j : ℕ+`,
  - and (eventually) a current equality `T = ∑ m_j • [V_j]`.

**Minimal new interface to keep proof track compiling**:

- Introduce a new “real theorem” interface WITHOUT breaking existing code:
  - `class HarveyLawsonKingData …` with field:
    - `decompose (hyp) : ∃ (data), …`
  - Prove `cone_positive_produces_cycle_real` assuming this class, in a new file/namespace.
  - Keep the current stub theorem used by proof track until the decomposition is actually implemented.

---

## Step 5 — Chow / GAGA becomes real (or explicitly assumed)

### Goal (TeX)
Analytic subvarieties of a projective complex manifold are algebraic (Chow + Serre GAGA).

### File to change

#### `Hodge/Classical/GAGA.lean` (PRIMARY)

**Current “semantic shortcut”**:
- `IsAnalyticSet_isAlgebraicSet` / `IsAlgebraicSet_isAnalyticSet` are implemented by mirroring inductive constructors, not by actual AG/analytic geometry.

**Two acceptable paths**:

1. **Real path**: replace these with real Mathlib-backed algebraic geometry facts (likely huge).
2. **Staged path (recommended)**: package Chow/GAGA as an explicit assumption:
   - `class ChowGAGAData (X) : Prop := (analytic_to_algebraic : …)`
   - use this in the “real spine” theorem, then later eliminate it.

**Minimal interface**:
- A function/theorem:
  - `(V : AnalyticSubvariety n X) → ∃ W : AlgebraicSubvariety n X, W.carrier = V.carrier`.

---

## Step 6 — Only after Steps 1–5: define `cycleClass` from geometry

### Goal (TeX)
Make the cohomology class of a cycle depend on the **geometric support** via a real fundamental class / PD form, and prove it equals `[γ]` for the cycle produced by the SYR→HL→GAGA pipeline.

### Files to change

#### `Hodge/Classical/CycleClass.lean`

**Current placeholder**:
- `poincareDualFormExists` is Z-dependent only via `hausdorffMeasure2p` which is a Dirac/basepoint proxy, not a real PD form construction.

**Replace with** (minimum viable correctness):
- A new interface `PoincareDualFormData` that connects:
  - integration over `Z` (as a current),
  - wedge pairing over `X`,
  - and Stokes descent to cohomology.

#### `Hodge/Analytic/Currents.lean`

**Explicit axiom to remove eventually**:
- `private axiom stokes_property_univ_axiom …`

For TeX-level faithfulness, replace this by:
- either a real Stokes theorem on the (assumed) closed manifold,
- or an explicit *assumption interface* used only in the PD/fundamental-class layer.

#### `Hodge/Classical/GAGA.lean`

**Current proof-track-safe shortcut** (as of 2026-01-25):
- `SignedAlgebraicCycle.cycleClass := ofForm representingForm …`

**Plan to revert to TeX semantics**:
- Introduce a parallel definition first:
  - `SignedAlgebraicCycle.cycleClass_geom := ofForm (FundamentalClassSet … support) …`
- Prove the bridge theorem for the produced cycles:
  - `cycleClass_geom(Z_from_Spines(γ)) = ofForm γ`
- Only after the bridge exists, switch `cycleClass` to the geometric definition.

**Exactly what to add back at the final switch**:
- A (nontrivial) witness lemma/field that `[γ] = [Z.support]` in de Rham cohomology, now proved using:
  - fixed-class SYR bookkeeping,
  - calibrated limit properties,
  - HL/King decomposition,
  - and Chow/GAGA algebraization.

---

## “Definition of done” (semantic closure)

You are done when:

1. `hodge_conjecture'` still passes `DependencyCheck` (only standard axioms), **and**
2. `SignedAlgebraicCycle.cycleClass` is defined from **geometry** (support → fundamental class/PD), **and**
3. the proof uses the TeX spine end-to-end:
   - SYR sequence exists and is nontrivial,
   - glue-gap is a real flat-norm / filling estimate,
   - realization-from-almost produces a calibrated limit,
   - HL/King turns calibrated current into holomorphic chain,
   - Chow/GAGA makes analytic components algebraic,
   - cycle class is computed from the produced algebraic cycle and equals `[γ]`.

---

## Suggested PR breakdown (recommended)

- PR1: Add “real” microstructure current (parallel defs), keep proof track unchanged.
- PR2: Add real glue-gap estimate + mass/flat control, still parallel.
- PR3: Tighten realization-from-almost hypotheses + Wirtinger/comass lemma.
- PR4: Replace HL stub with a real interface (or implement in stages).
- PR5: Package Chow/GAGA as explicit interface (or implement).
- PR6: Introduce geometric cycleClass in parallel and prove equality for spine-produced cycles.
- PR7: Flip proof track to geometric cycleClass and delete old shortcuts.

