# Stage 2 (A2): Integration Currents — Strategy

Stage 2 of `tex/archive/HodgePlan-mc-28.1.26.rtf` asks for a real construction of integration
currents:

- \([Z](\omega) := \int_Z \iota^* \omega\)
- Stokes: \(\partial[Z] = [\partial Z]\)

This note records a realistic Lean development path given current Mathlib support.

## 1. What Mathlib gives us today

### 1.1 Measure theory primitives

Mathlib has:

- robust `MeasureTheory` integration for measurable functions
- Hausdorff measure:
  - `Mathlib.MeasureTheory.Measure.Hausdorff` (notation `μH[d]`)

Hausdorff measure is a natural base for rectifiable-set integration and GMT currents.

### 1.2 Manifolds and smoothness (but not “integration of differential forms”)

Mathlib’s manifold library is strong for:

- `ChartedSpace`, `IsManifold`, `ContMDiff`, `MFDeriv` (smoothness / derivatives)

But a ready-made “integrate a differential form over an oriented submanifold” API is not presently
available at the level required by Stage 2. So Stage 2 is real new development.

## 2. Recommended construction order (small → large)

### Step A: top-degree integration on a compact oriented manifold

Goal: define \(\int_X \eta\) for a top-degree form \(\eta\) on a compact oriented manifold \(X\).

Lean path:

- define a volume measure on `X` (from a volume form / density),
- define `∫ x, f x` for scalar `f`,
- relate a top-degree form \(\eta\) to a scalar density via the volume form.

Deliverable:

- `TopFormIntegral` module proving linearity and Stokes in the boundaryless case.

### Step B: integration over an embedded closed submanifold `Z ⊆ X`

Goal: define \(\int_Z \iota^*\omega\).

Data required:

- a submanifold structure on `Z` (at minimum: `Z` is a smooth embedded manifold),
- orientation on `Z`,
- a measurable structure / measure on `Z` compatible with the induced Riemannian metric.

Possible approach:

- define the measure on `Z` as the Hausdorff measure `μH[dim Z]` restricted to `Z`
  (requires `MetricSpace X` + induced metric),
- define pullback of forms along `ι : Z → X`,
- define pointwise pairing “form evaluated on orienting k-vector” to get a scalar integrand.

### Step C: Stokes theorem for compact manifolds with boundary

This is the first major theorem:

- if `Z` is a compact oriented manifold with boundary, then
  \(\int_Z d\alpha = \int_{\partial Z} \alpha\).

In Lean this likely needs:

- boundary charts / collar neighborhoods,
- change-of-variables for integrals in charts,
- partition of unity.

This is a large chunk of analysis/topology work.

## 3. Where this plugs into the current repo

Right now the proof track uses a `SubmanifoldIntegration` typeclass stub to stand in for Stage 2.

Stage 2 completion means:

- remove `SubmanifoldIntegration` as an *assumption interface* from the proof track,
- replace it by actual constructions + theorems (Stokes etc),
- then define integration currents `integrationCurrent` as a special case of `Current` on test forms.

## 4. Recommended next Lean files (new, off proof track first)

- `Hodge/Analytic/Stage2/TopFormIntegral.lean`
  - top-degree integral on compact manifolds
- `Hodge/Analytic/Stage2/SubmanifoldMeasure.lean`
  - induced measure on an embedded submanifold (Hausdorff or Riemannian volume)
- `Hodge/Analytic/Stage2/SubmanifoldIntegral.lean`
  - defines \(\int_Z \iota^* \omega\)
- `Hodge/Analytic/Stage2/Stokes.lean`
  - proves Stokes theorem for the needed classes of submanifolds
- `Hodge/Analytic/Stage2/IntegrationCurrent.lean`
  - defines `[Z]` as a current and proves `∂[Z] = [∂Z]`

## 5. Practical note

This stage is a genuine multi-week formalization effort even with parallel agents. A realistic
first milestone is to get:

- compact boundaryless Stokes: \(\int_X d\omega = 0\)

then extend outward.

