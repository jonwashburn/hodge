# Mathlib Leverage Survey: GAGA / Chow / Analytic vs Algebraic

This document answers a very specific question:

> What does the bundled Mathlib snapshot in this repo already provide for **complex analytic geometry** and **Chow/GAGA**, and what is missing?

The goal is to avoid reinventing existing Mathlib infrastructure while being honest about what is **not** available.

---

## Current repo situation (status quo)

The current proof track uses simplified notions:
- `IsAnalyticSet` ≈ “topologically closed” (in `Hodge/Classical/HarveyLawson.lean`).
- `IsAlgebraicSet` := “topologically closed” (in `Hodge/Classical/GAGA.lean`).

These are explicitly **forbidden** under the “no gotchas” spec and must be replaced by real notions.

---

## What Mathlib *does* have (high-level)

Mathlib has extensive libraries for:
- **Smooth manifolds / differential forms** (used heavily here already).
- **Measure theory + Hausdorff measure** (`MeasureTheory.Measure.hausdorffMeasure`, notation `μH[d]`).
- **Algebraic geometry (schemes)**: many modules under `Mathlib/AlgebraicGeometry/*`.

---

## What Mathlib appears *not* to have (as far as this repo currently uses)

Based on repo searches in the bundled snapshot:
- There is **no direct** `Chow`/`GAGA` theorem module discoverable by name (no `GAGA` hits in Mathlib sources).
- There is no obvious “complex analytic set = local holomorphic zero locus” framework integrated with:
  - the manifold `ChartedSpace` view used in this repo; or
  - projective schemes.

This likely means:
- We cannot “just import a theorem” that analytic subvarieties of complex projective manifolds are algebraic.
- We must build a bridge either:
  - from this repo’s manifold model to Mathlib schemes, or
  - inside this repo, by developing a local analytic-geometry layer and then proving Chow/GAGA in that layer.

---

## Concrete Mathlib modules we *are* already using (useful for real integration/GMT)

- `Mathlib/MeasureTheory/Measure/Hausdorff.lean`
  - defines Hausdorff measure (`MeasureTheory.Measure.hausdorffMeasure`)
  - gives invariance under isometries, etc.

This is relevant for the **SubmanifoldIntegration** semantic restoration: we can (and should) use `μH[d]` as the underlying measure rather than a zero measure.

---

## What we likely need to build in this repo (if “no gotchas” is the target)

### 1) A real notion of analytic subset (local holomorphic zero loci)

We likely need:
- a definition of (local) holomorphic functions in this manifold model;
- a definition: `IsAnalyticSet Z := ∀ x ∈ Z, ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ f₁..f_m holomorphic on U, Z ∩ U = {y | ∀ i, f_i y = 0}`.

### 2) A real notion of algebraic subset (projective algebraic zero loci)

Given the current typeclass `ProjectiveComplexManifold n X` is not yet tied to a scheme or an embedding, we likely need to extend it (semantically) with:
- an embedding `X ↪ ℂP^N` (or a charted version of projective space);
- a definition of algebraic subsets as common zero loci of homogeneous polynomials under that embedding.

### 3) Chow/GAGA proof strategy

Once analytic/algebraic are real:
- Prove: analytic subset of a projective complex manifold is algebraic.

This is a major development. It should be split into many bounded lemmas and likely require substantial new infrastructure.

---

## Immediate next step (actionable)

If we want agents to help **without gotchas**, a safe near-term bounded task is:
- create a doc-level map of candidate Mathlib algebraic geometry entry points (`Mathlib/AlgebraicGeometry/*`) and assess whether any existing “projective variety”/“closed immersion” infrastructure can be repurposed.

This avoids touching proof-track semantics until the integrator is ready to do the (necessarily cross-cutting) refactor.

