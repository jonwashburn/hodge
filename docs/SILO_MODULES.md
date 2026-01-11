# Siloed / Off‑Track Modules

This document records Lean modules that are **intentionally not required** for the main theorem
(`hodge_conjecture` / `hodge_conjecture'`) and therefore may contain:

- `sorry` statements
- additional “Classical Pillar” axioms
- experimental / refactor-in-progress code

## Proof‑Track Definition (What *must* stay clean)

For this repository, the **proof track** is the import graph of:

- `Hodge.Main` (public theorem `hodge_conjecture`)

The root module `Hodge` is intentionally minimal and imports only `Hodge.Main`.

## How to Build

- **Proof track only**:

```bash
lake build Hodge.Main
```

- **Siloed/off‑track umbrella**:

```bash
lake build Hodge.OffTrack
```

- **Everything (proof track + off track)**:

```bash
lake build Hodge.All
```

## Silo Inventory

### 1) Advanced analytic exterior derivative (experimental)

- **Module**: `Hodge.Analytic.Advanced`
- **Status**: intentionally excluded from `Hodge.Main` / `Hodge.Analytic`
- **Purpose**: a “real” chart-based exterior derivative and Leibniz rule infrastructure, to
  eventually replace the Classical-Pillar axioms in `Hodge.Analytic.Forms`.

Notes:
- `Hodge.Analytic.Advanced` contains the word `sorry` in documentation to flag WIP status;
  it is **not** imported by the main proof.

### 2) Kähler identities / sl(2) / Hard Lefschetz development path (supplementary)

These modules support a mathematically standard route to Hard Lefschetz via Kähler identities
and sl(2) representation theory, but they are **not** used by `Hodge.Main` at present.

- **Modules (entry points)**:
  - `Hodge.Classical.KahlerIdentities`
  - `Hodge.Classical.PrimitiveDecomposition` (**contains `sorry`**)
  - `Hodge.Classical.HardLefschetz`

### 3) Classical “toolbox” modules (not required by the main proof)

These are classical results that may be useful later, but are not needed to compile
`Hodge.Main`:

- `Hodge.Classical.Bergman`
- `Hodge.Classical.SerreVanishing`
- `Hodge.Classical.FedererFleming`

### 4) Category‑theoretic filtration infrastructure (not required by the main proof)

- `Hodge.CategoryTheory.Filtration` (and submodules)

### 5) Work‑in‑progress Hodge decomposition file (currently not imported)

- **File**: `Hodge/Cohomology/HodgeDecomposition.lean`
- **Status**:
  - not imported by `Hodge.Main`
  - **contains `sorry`**
  - currently **untracked in git** in this workspace (so it is *not* depended on by any tracked module)

## Modules with `sorry` *on* the proof track (NOT siloed)

These files are currently in the proof‑track import graph and therefore are **not**
considered “siloed” (even if the `sorry` occurs in a lemma that the main theorem does not use):

- `Hodge/Analytic/Currents.lean`
- `Hodge/Cohomology/Basic.lean`
- `Hodge/Kahler/Manifolds.lean`

