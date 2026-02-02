# Mathlib leverage survey (GAGA / Chow / analytic sets) — 2026-02-01

This note answers the playbook task **AG-05**: “what (if anything) exists in bundled Mathlib for
analytic/algebraic geometry in the directions needed by the TeX spine?”

It is **not** a proof plan; it is an inventory of what is available *right now* in this repo’s
vendored Mathlib snapshot, plus the minimal conclusions for the next semantic-restoration steps.

---

## 1. Complex manifolds / holomorphic functions (available)

Mathlib provides complex-manifold infrastructure sufficient to *state* “local holomorphic zero loci”.

- **Module**: `Mathlib.Geometry.Manifold.Complex`
- **Predicate used in-repo**: `MDifferentiableOn (𝓒_complex n) (𝓘(ℂ, ℂ)) f U`
  - This is used as the “holomorphic on `U`” predicate in:
    - `Hodge/AnalyticSets.lean` (`Hodge.AlgGeom.IsAnalyticSetZeroLocus`)

Practical takeaway:
- We can define analytic sets as “locally common zero loci of finitely many holomorphic functions”
  using Mathlib’s manifold differentiability predicate.

---

## 2. Hausdorff measure (available)

Mathlib has a genuine definition of Hausdorff measure on (e)metric spaces.

- **Module**: `Mathlib.MeasureTheory.Measure.Hausdorff`
- **Definition**: `MeasureTheory.Measure.hausdorffMeasure (d : ℝ) : Measure X`
- **Notation (scoped)**: `μH[d]`

Practical takeaway:
- The project can (and now does) use real Hausdorff measure primitives where appropriate, rather than
  `0`-measure stubs.

---

## 3. GAGA / Chow theorem (NOT found in this Mathlib snapshot)

Searches in vendored Mathlib for canonical strings (`GAGA`, `Chow theorem`, `Serre GAGA`,
`Lefschetz (1,1)`, `hodge_conjecture`) returned **no relevant modules** implementing:

- Chow’s theorem (projective analytic ⇒ algebraic);
- Serre’s GAGA equivalence;
- Hodge conjecture (or its standard major special cases).

Practical takeaway:
- The project cannot “just import Mathlib” for Chow/GAGA; the needed results must be developed
  in-repo (or the repository must be reorganized to work in a scheme-theoretic setting where
  something equivalent is already formalized — but that is also not presently available here).

---

## 4. De Rham theorem / Poincaré duality for manifolds (NOT found)

Searches for “de Rham” / “Poincaré duality” in vendored Mathlib did not locate a ready-to-use
development of:

- the de Rham theorem for smooth manifolds;
- Poincaré duality in a form that produces a representing differential form from a cycle/current.

Practical takeaway:
- The “cycleClass_geom from support via fundamental class / integration current” pillar will require
  substantial new infrastructure inside this repo (or a different formalization approach).

---

## 5. Current repo scaffolding relevant to analytic/algebraic semantics

Independent of Mathlib, the repo already contains a **mathematically faithful analytic-set definition**
as local holomorphic zero loci:

- `Hodge/AnalyticSets.lean`:
  - `Hodge.AlgGeom.IsAnalyticSetZeroLocus`

This can be used as the semantic target for replacing the “analytic = closed” placeholder in
`Hodge/Classical/HarveyLawson.lean` once the Harvey–Lawson/King pillar provides real analytic output.

# Mathlib leverage survey: Chow/GAGA + analytic/algebraic sets (2026-02-01)

This note records what is (and is not) available in the bundled Mathlib snapshot for implementing the **non-stub** versions of:

- complex **analytic sets** (local holomorphic zero loci);
- **algebraic** sets/varieties (Zariski-closed / scheme-theoretic);
- **Chow’s theorem** / **GAGA** in the projective setting.

It is intended to support the “no gotchas” cleanup in `Hodge/Classical/GAGA.lean` and `Hodge/Classical/HarveyLawson.lean`.

---

## Summary (high signal)

- **No `Chow` / `GAGA` theorems found** in this Mathlib snapshot (no modules or theorems matching those names).
- **No ready-made “analytic set” structure** found (nothing like `IsAnalyticSet` / “locally holomorphic zero locus” packaged).
- There *is* substantial **algebraic geometry** infrastructure for projective schemes (`AlgebraicGeometry/ProjectiveSpectrum/*`), and there is **complex manifold / holomorphic** infrastructure (`Geometry/Manifold/Complex.lean`, plus complex analysis).

Conclusion: **Chow/GAGA and analytic-set theory will need to be built in-repo** (or the project must be refactored to use a different existing library).

---

## Evidence (searches run)

From repo root, searching inside bundled Mathlib:

```bash
# Chow / GAGA names
rg -n \"GAGA|Chow\" .lake/packages/mathlib/Mathlib

# “analytic set”/holomorphic keywords
rg -n \"analytic set|IsAnalytic|holomorphic|ComplexAnalytic\" .lake/packages/mathlib/Mathlib

# projective algebraic geometry modules
rg -n \"ProjectiveSpace|Projective\" .lake/packages/mathlib/Mathlib/AlgebraicGeometry
```

Results (representative):

- `GAGA|Chow`: **no matches**.
- holomorphic/complex analysis hits: mostly complex analysis and complex manifolds; no analytic-set definitions.
- projective AG hits:
  - `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean`
  - `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean`
  - `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean`
  - `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean`
  - `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean`

---

## What *is* available (likely useful building blocks)

### Complex manifolds / holomorphic functions

- `Mathlib/Geometry/Manifold/Complex.lean`
- Many complex-analysis modules under `Mathlib/Analysis/Complex/*`

These can support:
- defining holomorphic functions in charts;
- local analytic geometry (if we build the “common zero locus of holomorphic functions” layer).

### Algebraic geometry (projective)

- `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/*`
- broader scheme-theoretic infrastructure in `Mathlib/AlgebraicGeometry/*`

These can support:
- defining projective varieties/schemes and Zariski-closed subsets;
- expressing “algebraic subset” in a non-stub way.

---

## What is missing (must be implemented for “no gotchas”)

To eliminate the explicit gotchas:

- `IsAnalyticSet := IsClosed` in `Hodge/Classical/HarveyLawson.lean`
- `IsAlgebraicSet := IsClosed` in `Hodge/Classical/GAGA.lean`

we appear to need new in-repo development covering at least:

- **Analytic sets** on a complex manifold:
  - locality (`∀ x, ∃ neighborhood U, ∃ finite family fᵢ holomorphic on U, Z ∩ U = {x | ∀ i, fᵢ x = 0}`),
  - closure under finite unions/intersections,
  - basic examples (∅, univ, hyperplanes) proved from the definitions.
- **Algebraic sets** on a projective manifold:
  - a definition as Zariski-closed (scheme-theoretic closed subset, or polynomial zero-locus in projective space),
  - closure properties,
  - bridge to the ambient complex manifold topology.
- **Chow/GAGA**:
  - analytic subset of projective space/manifold ⇒ algebraic subset,
  - the “projective manifold” identification used in this repo’s spine.

---

## Immediate repo follow-ups

- Update the “gotchas” index entries for `IsAnalyticSet` / `IsAlgebraicSet` to point to the above missing layers.
- Decide on the representation choice:
  - **scheme-first** (use `AlgebraicGeometry` and define analytic sets separately, then prove equivalence in projective case), or
  - **polynomial-first** (define algebraic sets as polynomial zero loci in projective charts, then connect to schemes later).

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

