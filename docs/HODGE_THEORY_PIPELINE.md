# Hodge Theory Pipeline (⋆ → δ → Δ → Harmonic)

This document summarizes the current “Hodge theory pipeline” in the Lean codebase and how the
modules connect.

## Scope / proof-track note

- The **proof track** entry point is `Hodge.lean` → `Hodge/Main.lean` → `Hodge/Kahler/Main.lean`.
  It is intentionally minimal and does **not** import the off-track Hodge-theory development.
- The pipeline below is therefore **off proof track** (unless explicitly imported by an off-track
  umbrella).

## High-level pipeline

Classically, on a compact Kähler manifold:

1. **Hodge star**: \(⋆ : Ω^k → Ω^{2n-k}\)
2. **Codifferential**: \(δ = ±⋆\,d\,⋆ : Ω^k → Ω^{k-1}\)
3. **Hodge Laplacian**: \(Δ = dδ + δd : Ω^k → Ω^k\)
4. **Harmonic forms**: \(ω\) is harmonic iff \(Δω = 0\), and (under L² theory) iff \(dω = 0\) and \(δω = 0\)

## Where things live in this repo

### Hodge star ⋆

- **Global placeholder ⋆**: `Hodge/Analytic/Norms.lean`
  - Provides `hodgeStar` (currently via `HodgeStarData.trivial`, i.e. `⋆ = 0`).
  - This is the ⋆ used by `Codifferential` right now.

- **Fiber-level “future” ⋆ infrastructure**: `Hodge/Analytic/HodgeStar/*`
  - `Hodge/Analytic/HodgeStar/FiberStar.lean`: `fiberAltInner`, `fiberHodgeStar_construct` (currently stubbed as `0`)
  - `Hodge/Analytic/HodgeStar/Involution.lean`: fiber-level involution statement (currently stubbed: `⋆⋆ = 0`)
  - `Hodge/Analytic/HodgeStar/Smoothness.lean`: placeholder for proving smoothness of ⋆ on sections

### Codifferential δ = ±⋆d⋆

- `Hodge/Analytic/Laplacian/Codifferential.lean`
  - Defines `codifferential` using the formula \(δ = ±⋆ d ⋆\).
  - With the current placeholder ⋆, δ is also trivial; the file provides basic algebraic lemmas and `codifferential_squared_zero`.

### Laplacian Δ = dδ + δd

- **Structural Δ (dδ + δd)**: `Hodge/Analytic/Laplacian/HodgeLaplacian.lean`
  - Defines `laplacian_construct` / `hodgeLaplacian_construct` in the intended “operator” shape.
  - Currently simplifies to `0` because δ is trivial, but the definition is arranged so it can be upgraded later.

- **L²-oriented Laplacian (dd* + d*d)**: `Hodge/Analytic/HodgeLaplacian.lean`
  - Defines `L2InnerProduct`, `hodgeDual` (d*), and `hodgeLaplacian` as \(Δ = dd^* + d^*d\).
  - This file is where “analytic” Laplacian facts (self-adjointness, non-negativity, kernel characterization) are expected to live.

### Harmonic forms

- **Structural harmonic interface (based on `Laplacian/` Δ)**: `Hodge/Analytic/Laplacian/HarmonicForms.lean`
  - Defines `IsHarmonic` as `Δω = 0` for the `Laplacian/` operator.
  - Provides a stub-friendly “closed+coclosed” characterization (documented as such in the file).

- **L²-oriented harmonic theory (based on `Hodge/Analytic/HodgeLaplacian.lean`)**:
  `Hodge/Analytic/HarmonicForms.lean`
  - Intended for the “real” Hodge decomposition path (harmonic representatives, orthogonality, etc.).

## Verification / wiring tests

- `Hodge/Analytic/Laplacian/ConnectionTests.lean`
  - A lightweight compile-time sanity check that the ⋆/δ/Δ/harmonic interfaces compose.

## Current state (2026-01-19)

- The **proof track** is clean (no custom axioms, no sorries).
- The **pipeline modules** exist and type-check; many operators are still semantic stubs while the
  integration/L² infrastructure is being completed.

