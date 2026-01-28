# Stage 3+4 (A3): GMT Core + Calibration + Harvey–Lawson — Strategy

Stages 3–4 of the plan are the “GMT engine”:

- define mass and flat norm on currents,
- prove compactness / existence of flat limits (Federer–Fleming),
- connect calibrated currents to holomorphic chains (Harvey–Lawson/King).

This note records what is realistic in Lean/Mathlib today and a proposed incremental path.

## 1. Mathlib baseline

Mathlib has:

- strong measure theory and functional analysis (`MeasureTheory`, locally convex spaces),
- Hausdorff measure `μH[d]`:
  - `Mathlib.MeasureTheory.Measure.Hausdorff`

But Mathlib does **not** currently provide:

- integral currents / rectifiable currents as in Federer,
- flat norm and Federer–Fleming compactness,
- calibrated-current regularity results (Harvey–Lawson/King).

So Stage 3–4 is largely new development (or a very large upstream effort).

## 2. Recommended “honest” decomposition of the GMT workload

### (A) Functional-analytic layer: currents as continuous linear maps

Once Stage 1 provides `Current := (TestFormSpace →L[ℝ] ℝ)`:

- mass can be defined as a dual seminorm (sup over comass ≤ 1 test forms),
- flat norm can be defined as an inf over decompositions `T = R + ∂S` (requires boundary operator).

This part is mostly topology/analysis on locally convex spaces and can be developed early.

### (B) Geometric layer: integration currents and rectifiable currents

Requires Stage 2 to build integration currents `[Z]`.

Then define:

- rectifiable currents as “finite sums of integration currents” + completion,
- integral currents as integer-multiplicity rectifiable currents with rectifiable boundary.

This is a large formalization of GMT definitions.

### (C) Compactness (Federer–Fleming)

The theorem is fundamentally analytic:

- bounds on mass + boundary mass imply precompactness in flat norm.

Lean path:

- define polyhedral chains and prove density,
- define flat norm as inf over decompositions,
- prove compactness via diagonal argument + tightness estimates.

### (D) Calibration theory + holomorphicity

This is the hardest: “calibrated ⇒ regular/holomorphic chain” requires serious regularity theory.

Realistic approach for the project:

- isolate the *minimum* calibration regularity statement needed for the Hodge pipeline,
- build it as a separate “classical pillar” module, likely requiring a dedicated long-term effort.

## 3. Harvey–Lawson/King integration points

In the Hodge pipeline, we need:

1. From a calibrated integral current `T`, extract an analytic subvariety support `V`
2. A decomposition `T = Σ mᵢ [Vᵢ]` (weighted holomorphic chain)
3. Cohomological representation: `T` represents the target Hodge class

These correspond to deep theorems (structure + regularity).

## 4. Recommended next Lean files (new, off proof track first)

- `Hodge/GMT/Stage3/Mass.lean`
  - mass as a dual seminorm on `Current`
- `Hodge/GMT/Stage3/FlatNorm.lean`
  - flat norm definition and basic inequalities
- `Hodge/GMT/Stage3/Compactness.lean`
  - statement + “infrastructure lemmas”; keep the main theorem isolated
- `Hodge/GMT/Stage4/Calibration.lean`
  - definitions of calibration + calibration defect
- `Hodge/GMT/Stage4/HarveyLawsonKing.lean`
  - isolate the deep theorem statement(s) needed for the pipeline

## 5. Practical staging

Even in the optimistic multi-agent plan, Stage 3–4 is where the project becomes “real GMT”.
The best immediate win is to ensure Stage 1–2 produce the right functional-analytic objects so that
Stage 3–4 is a matter of proving theorems about those objects, not refactoring foundations later.

