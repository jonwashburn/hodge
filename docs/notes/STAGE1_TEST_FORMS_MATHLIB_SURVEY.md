# Stage 1 (A1): Test Form Spaces — Mathlib Survey + Repo Integration Plan

This note is the Stage 1 “bridge” between the plan in `tex/archive/HodgePlan-mc-28.1.26.rtf` and
what Mathlib already provides today.

## 1. Key discovery: Mathlib already has LF test-function spaces

Mathlib has a serious distribution theory framework for **Euclidean domains**:

- `Mathlib.Analysis.Distribution.TestFunction`
- `Mathlib.Analysis.Distribution.Distribution`

In this framework:

- `𝓓(Ω, F)` is the LF space of smooth (`C^∞`) functions `E → F` with compact support contained in
  an open set `Ω : TopologicalSpace.Opens E`, where `E` is a real finite-dimensional normed space.
- `𝓓'(Ω, F)` (distributions) are continuous linear maps out of `𝓓(Ω, ℝ)` (scalar test functions).

This is *exactly* the functional-analytic direction demanded by Stage 1 of the plan: define
currents as continuous linear maps on a test-form LF-space, not as bespoke structures with ad hoc
boundedness fields.

## 2. How this connects to differential forms in this repo

In this repo, a smooth k-form (fiberwise object) is represented as a smooth section:

- `SmoothForm n X k` has `as_alternating : X → FiberAlt n k`
- where `FiberAlt n k := (TangentModel n) [⋀^Fin k]→L[ℂ] ℂ`

So **on the Euclidean model space** `E := EuclideanSpace ℂ (Fin n)`:

- a “Euclidean k-form” can be treated as a smooth function `E → FiberAlt n k`
- a “Euclidean test k-form” should be a compactly supported smooth function `E → FiberAlt n k`

Mathlib’s `𝓓(Ω, F)` can therefore model *Euclidean test k-forms* by taking `F := FiberAlt n k`.

## 3. What we already added to the repo

### 3.1 Compact-support test forms (manifold-level seed)

- `Hodge/Analytic/TestForms.lean`

Defines:

- `TestForm n X k := { ω : SmoothForm n X k // HasCompactSupport ω.as_alternating }`

This is a **seed** for Stage 1 (it gives the right underlying set and basic algebra), but it does
**not yet** provide the LF / Fréchet topology.

### 3.2 Euclidean LF test forms via Mathlib distributions

- `Hodge/Analytic/DistributionTestForms.lean`

Defines:

- `EuclidTestForm n k Ω := 𝓓(Ω, FiberAlt n k)`
- `EuclidCurrent n k Ω := EuclidTestForm n k Ω →L[ℝ] ℝ`

This is a concrete, compiling bridge to Mathlib’s LF-space machinery.

## 4. Next coding steps to complete Stage 1 (real work)

### Step A (Euclidean): define exterior derivative on `EuclidTestForm`

Goal: a **continuous linear map**

- `d : EuclidTestForm n k Ω →L[ℝ] EuclidTestForm n (k+1) Ω`

This requires implementing the Euclidean exterior derivative at the level of functions into
`FiberAlt`, and proving it preserves compact support and is continuous in the LF topology.

### Step B (Euclidean): define boundary of a current by duality

Once `d` exists as above, define:

- `∂ : EuclidCurrent n (k+1) Ω →L[ℝ] EuclidCurrent n k Ω`

by precomposition with `d`.

### Step C (Manifold): transport test-form LF structure from charts

This is the hard manifold step:

- cover compact `X` by finitely many charts,
- represent a global test form by a family of Euclidean test forms plus compatibility,
- define the LF/Fréchet topology as a suitable subspace topology / inductive limit.

This is where we likely need additional Mathlib infrastructure (or upstream PRs).

### Step D: migrate `Current` away from bespoke structure

Ultimately:

- remove the bespoke `Current` fields `bound` and `boundary_bound`,
- define `Current` as `ContinuousLinearMap` out of the true test-form space.

## 5. Bottom line

- Stage 1 is *feasible* in Lean because Mathlib already has LF test-function spaces in Euclidean
  domains.
- The main engineering challenge is transporting this from Euclidean spaces to manifolds in a way
  compatible with the Hodge proof pipeline.

