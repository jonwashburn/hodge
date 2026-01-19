# Classical Pillars Summary (Round 2)

This is a short “Round 2” summary for the **Classical Pillars** / **semantic stubs**
in the Hodge formalization.

The **authoritative global list** lives in:
- `docs/notes/CLASSICAL_PILLARS.md`

This document focuses on the *Agent 5 (GMT / classical geometry) surface area* and
where the remaining deep inputs are represented in the codebase.

---

## Repo policy: no new `axiom` declarations

The project is protected by:
- `Hodge/AxiomGuard.lean`
- `scripts/audit_stubs.sh` / `scripts/verify_proof_track.sh`

Deep results are tracked as:
- documented **stubs** (`sorry`) in off-proof-track modules, and/or
- documented **placeholders** (e.g. `:= 0`) where the surrounding API is the focus.

This keeps the **proof track** clean while still allowing infrastructure work to proceed.

---

## Agent 5: GMT / Classical “Pillars” (current state)

### Federer–Fleming compactness (GMT)

- **File**: `Hodge/GMT/FedererFleming.lean`
- **Primary stub**:
  - `Hodge.GMT.federer_fleming_compactness` (returns a convergent subsequence structure)
- **Related stub**:
  - `Hodge.GMT.mass_lsc_flatNorm` (mass lower semicontinuity under flat convergence)
- **References**:
  - Federer–Fleming, *Normal and Integral Currents*, Annals of Math. (1960)
  - Federer, *Geometric Measure Theory* (1969), Ch. 4
  - Simon, *Lectures on Geometric Measure Theory*

### Harvey–Lawson structure theorem (calibrated currents → analytic cycles)

- **File**: `Hodge/GMT/HarveyLawsonTheorem.lean` (wrapper)
- **Underlying semantic stub**:
  - `Hodge/Classical/HarveyLawson.lean` (returns trivial data; not on proof track)
- **Reference**:
  - Harvey–Lawson, *Calibrated geometries*, Acta Math. (1982)

### GAGA / Chow (analytic ↔ algebraic)

- **File**: `Hodge/AlgGeom/GAGA.lean` (wrapper)
- **Underlying development**:
  - `Hodge/Classical/GAGA.lean` (inductive “algebraic set” interface + bridge)
- **References**:
  - Serre, *Géométrie algébrique et géométrie analytique* (1956)
  - Hartshorne, *Algebraic Geometry* (1977), Appendix B

---

## What “done” means for Round 2

For this round, Agent 5 aims to:
- keep the proof track axiom list unchanged (`propext`, `Classical.choice`, `Quot.sound`)
- avoid `axiom` declarations
- keep Classical Pillars isolated + clearly documented
- reduce the number of stubs where routine lemmas are provable (e.g. nonnegativity, nonemptiness)

