# Classical Pillars (Comprehensive List)

This document is the **comprehensive list of Classical Pillars** used in this repository.

**Goal**: keep the proof-track free of ad-hoc interface axioms, while allowing progress by
isolating deep, literature-backed theorems as **Classical Pillars**.

## Axiom taxonomy

- **Lean system axioms** (always expected): `Classical.choice`, `propext`, `Quot.sound`.
- **Project axioms / stubs**:
  - We avoid adding new `axiom` declarations.
  - Deep results are tracked as:
    - documented **stubs** (`sorry`) in **off-proof-track** modules, and/or
    - documented placeholder definitions (e.g. `:= 0`) where the surrounding API is the focus.

**Proof-track enforcement**:
- `Hodge/AxiomGuard.lean`
- `scripts/audit_stubs.sh`
- `scripts/verify_proof_track.sh`

---

## Classical Pillars (authoritative list)

This list is maintained in `docs/notes/CLASSICAL_PILLARS.md`.  We mirror it here because the
operational plan’s Round‑3 checklist requires a top-level `docs/CLASSICAL_PILLARS.md`.

Each pillar below should be understood as: **standard theorem in the literature**, currently not
fully formalized, but isolated and documented so the surrounding infrastructure can be developed.

### GMT / classical geometry pillars (Agent 5 surface area)

- **Federer–Fleming compactness** (`Hodge/GMT/FedererFleming.lean`)
  - **Meaning**: compactness / subsequence convergence for integral currents with bounded mass and boundary mass.
  - **Refs**: Federer–Fleming (1960); Federer (1969), Ch. 4.
  - **What’s needed to prove**: polyhedral approximation + slicing + compactness arguments on manifolds.

- **Harvey–Lawson structure theorem** (`Hodge/Classical/HarveyLawson.lean` and wrappers in `Hodge/GMT/HarveyLawsonTheorem.lean`)
  - **Meaning**: calibrated currents are represented by analytic cycles with multiplicities.
  - **Refs**: Harvey–Lawson (1982).
  - **What’s needed to prove**: full calibrated-geometry GMT + regularity theory.

- **GAGA / Chow** (`Hodge/Classical/GAGA.lean` and wrapper `Hodge/AlgGeom/GAGA.lean`)
  - **Meaning**: analytic subvarieties of projective manifolds are algebraic.
  - **Refs**: Serre (1956); Hartshorne (1977), Appendix B.
  - **What’s needed to prove**: coherent sheaves + comparison theorems (large Mathlib development).

### Global pillars (full repo)

For the full list (including non-Agent‑5 pillars used elsewhere in the proof pipeline), see:
- `docs/notes/CLASSICAL_PILLARS.md`
- `docs/plans/PROOF_CHAIN_AXIOMS.md`

---

## Round‑3 note

Round‑3 focuses on:
- consolidating Classical Pillar documentation,
- ensuring test files exist and compile,
- keeping proof-track axioms unchanged,
- and eliminating avoidable stubs where the current development makes them vacuous.

