# Classical Pillars Summary

This is a short summary for the **Classical Pillars** / **semantic stubs** in the Hodge
formalization.

The authoritative global list lives in:
- `docs/notes/CLASSICAL_PILLARS.md` (source of truth)
- `docs/CLASSICAL_PILLARS.md` (Round‑3/4 “top-level” mirror for checklist tooling)

This document focuses on the *GMT / classical geometry* surface area (Agent 5) and where the
remaining deep inputs are represented in the codebase.

---

## Repo policy: no new `axiom` declarations

The project is protected by:
- `Hodge/AxiomGuard.lean`
- `scripts/audit_stubs.sh` / `scripts/verify_proof_track.sh`

Deep results are tracked as:
- documented **stubs** (sometimes `sorry`) in off-proof-track modules, and/or
- documented **placeholders** (e.g. `:= 0`) where the surrounding API is the focus.

This keeps the **proof track** clean while still allowing infrastructure work to proceed.

---

## GMT / Classical “Pillars” (Agent 5 surface area)

### Federer–Fleming compactness (GMT)

- **File**: `Hodge/GMT/FedererFleming.lean`
- **Key theorems**:
  - `Hodge.GMT.federer_fleming_compactness`
  - `Hodge.GMT.mass_lsc_flatNorm`
- **Status note**:
  - In the current repo stub regime, the `IntegralPolyhedralChain'` predicate has no nonzero
    generators, so the “integral currents” API collapses to `0`.  Consequently these theorems are
    provable in a *vacuous* way (and the file has 0 `:= sorry` stubs), while still serving as the
    correct API surface for the intended GMT development.
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

## What “done” means for the GMT pillar layer

- keep the proof track axiom list unchanged (`propext`, `Classical.choice`, `Quot.sound`)
- avoid introducing new `axiom` declarations
- keep Classical Pillars isolated + clearly documented
- prove routine helper lemmas where possible, even in the stub regime

