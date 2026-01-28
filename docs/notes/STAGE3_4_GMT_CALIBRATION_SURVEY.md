# Stage 3+4 (A3): GMT Core + Calibration Survey

This note summarizes:

- what Mathlib already provides that is relevant to GMT (mass/comass, Hausdorff measure, rectifiability/currents if any),
- what **this repo** currently does for `Current`, `mass`, `flatNorm`, and calibration,
- concrete next coding steps to move toward the plan in `tex/archive/HodgePlan-mc-28.1.26.rtf`.

## 1. Mathlib: relevant existing infrastructure

### 1.1 Hausdorff measure / geometric measure theory primitives

Mathlib has a substantial measure-theory core, including Hausdorff measures:

- `Mathlib/MeasureTheory/Measure/Hausdorff`

This is the natural basis for defining “mass” of rectifiable chains/currents and for submanifold integration (if you model integration via Hausdorff measure restricted to submanifolds).

### 1.2 Compact support / test-function spaces

For Stage 1 (test forms) and Stage 3 (currents as distributions), Mathlib has a mature notion of compact support:

- `Mathlib/Topology/Algebra/Support` (Prop `HasCompactSupport`, closure lemmas)

This is already used by `Hodge/Analytic/TestForms.lean` in this repo as the first “Stage 1” seed.

### 1.3 Differential forms + exterior derivative

Mathlib has manifold differential forms (and `ContMDiffForm.extDerivForm`) and smooth manifold derivatives. This repo currently wraps that into `smoothExtDeriv` (see `Hodge/Analytic/Forms.lean`).

### 1.4 Currents / rectifiable currents

As of this sweep, Mathlib does **not** appear to provide a ready-to-use “integral current / rectifiable current” API matching Federer (mass, boundary, flat norm, compactness) in a way that can directly replace the project’s GMT layer.

So Stages 3–4 are expected to be a significant new development (either in-project or upstream).

## 2. This repo: current GMT + calibration model

### 2.1 `Current`

File: `Hodge/Analytic/Currents.lean`.

Current definition today is **bespoke**:

- `Current n X k` is a structure with:
  - `toFun : SmoothForm n X k → ℝ`
  - a bundled linearity axiom `is_linear`
  - a bundled continuity axiom `is_continuous : Continuous toFun`
  - a bundled seminorm bound `bound : ∃ M, ∀ ω, |T(ω)| ≤ M * ‖ω‖`
  - a bundled “boundary boundedness” field `boundary_bound` so `∂T` is definable

This is *not* the plan’s Stage 1/Stage 3 model (which wants `Current` = `ContinuousLinearMap` out of an LF-space of compactly supported test forms, so boundedness is derived, and boundary is defined by duality with `d`).

### 2.2 Mass and flat norm

File: `Hodge/Analytic/Currents.lean`, `Hodge/Analytic/FlatNorm.lean`.

- `mass` is implemented as a supremum over form evaluations with `comass ≤ 1`.
- `flatNorm` exists and supports basic lemmas (`flatNorm_nonneg`, `flatNorm_zero`, etc.).

This is structurally aligned with GMT, but still sits on the project’s current “forms as a normed space” model, not on an LF-space of test forms.

### 2.3 Calibration theory

File: `Hodge/Analytic/Calibration.lean`.

- `CalibratingForm` is a closed form with `comass ≤ 1`.
- `calibrationDefect T ψ := mass(T) - T(ψ.form)`.
- Basic inequalities and “defect ≥ 0” are proved using the repo’s mass/comass lemmas.

This *is* the correct shape (and should survive the Stage 1 → Stage 3 refactor), but the meaning of continuity and evaluation should eventually be moved to the test-form topology and the distributional framework.

## 3. What must change to match the plan (Stages 3–4)

### 3.1 Replace `Current` by `ContinuousLinearMap` on test forms

Target: replace

- `structure Current ...` (bespoke fields)

with:

- `def TestFormSpace k :=` LF-space of compactly supported smooth `k`-forms
- `def Current k := (TestFormSpace k) →L[ℝ] ℝ` (or `→L[ℂ] ℂ` depending on convention)

This removes:

- the manual `bound` field
- the manual `boundary_bound` field

and makes “boundary” definitional:

- `(∂T)(ω) := T(dω)` with a sign convention.

### 3.2 Distributional exterior derivative (Stokes without typeclass)

Stage 2 wants “integration currents” to be actual integrals over submanifolds, and Stage 3 wants Stokes to be a theorem. Concretely:

- define `integrationCurrent Z : Current`
- prove `∂[Z] = [∂Z]`
- for closed `Z`, deduce `∂[Z] = 0`

The current repo still relies on the `SubmanifoldIntegration` interface (a class of axioms) to get Stokes-like statements. That must be deleted/replaced by real theorems during Stages 2–3.

### 3.3 Federer–Fleming compactness + Harvey–Lawson/King regularity

These are the real hard pillars:

- Compactness for integral currents with bounded mass + boundary mass
- Regularity: calibrated integral currents are holomorphic chains

No “toy” implementation should be accepted on the final track. The Stage 0 quarantine work removed the worst “everything is 0” regime, but the real theorem work remains to be done.

## 4. Concrete next coding steps (what we can do incrementally)

### Step A (Stage 1 continuation): finish test-form type and basic operations

File started:

- `Hodge/Analytic/TestForms.lean`

Next:

- define wedge and `smoothExtDeriv` on `TestForm` and prove compact-support closure:
  - `HasCompactSupport (ω ⋏ η)` given compact support of `ω` and `η`
  - `HasCompactSupport (dω)` given compact support of `ω`

This is a key prerequisite for defining boundary by duality later.

### Step B (Stage 3 preparation): define `Current₀` as `ContinuousLinearMap` on `TestForm`

Introduce a new definition (do not break the existing proof track yet):

- `def CurrentCLM (k) := (TestForm n X k) →L[ℝ] ℝ`

Then add adapter functions:

- `Current → CurrentCLM` and (temporarily) `CurrentCLM → Current` using the current normed model

This lets us migrate lemmas one by one.

### Step C (Stage 3): redefine boundary for `CurrentCLM`

- `boundaryCLM (T : CurrentCLM (k+1)) : CurrentCLM k := fun ω => T (dω)` (with a sign)

Prove:

- linearity is automatic
- continuity follows once `d : TestForm k → TestForm (k+1)` is continuous in the chosen topology

### Step D (Stage 3): re-prove mass/flat norm API on `CurrentCLM`

Once the topology is in place and `TestForm` has a norm/seminorm family, rebuild:

- `mass : CurrentCLM → ℝ≥0∞`
- `flatNorm : CurrentCLM → ℝ≥0∞`

and prove the “calibration inequality” in the new setting.

### Step E (Stage 4): calibrations + holomorphic chain regularity

Keep the existing `CalibratingForm` API but migrate its theorems to the new current model.

## 5. Status

- Stage 0 “toy GMT / toy analytic geometry” induction-based hazards are quarantined.
- Stage 1 now has a **seed** implementation of compactly supported smooth forms:
  - `Hodge/Analytic/TestForms.lean`

The remaining work in Stages 3–4 is large and will require dedicated development and (likely) upstream Mathlib contributions for LF topologies and current/rectifiability infrastructure.

