# Classical Pillars (Intentionally Kept Axioms)

This repo has two kinds of axioms:

- **Lean system axioms**: e.g. `Classical.choice`, `propext`, `Quot.sound`.
- **Project axioms**: mathematical assumptions used by the Hodge proof development.

The **refactoring goal** (see `REFACTORING_PLAN.md`) is to eliminate *interface axioms*
coming from `opaque` / placeholder APIs, so that the only remaining project axioms are a
small set of **classical pillars**: deep theorems from the literature that are reasonable
to assume while the surrounding infrastructure is being formalized.

This document is the **authoritative list** of those classical pillars.

---

## Classical pillar axioms (target set = 13)

These thirteen are explicitly marked in Lean with `STATUS: CLASSICAL PILLAR` (or
`STATUS: STRATEGY-CRITICAL CLASSICAL PILLAR`) in their docstrings.

- **`mass_lsc`** (`Hodge/Analytic/Calibration.lean`)
  - **Meaning**: lower semicontinuity of mass under flat-norm convergence.
  - **Refs**: Federer–Fleming (1960); Federer (1969).

- **`exists_uniform_interior_radius`** (`Hodge/Kahler/Cone.lean`)
  - **Meaning**: uniform interior ball for the Kähler cone.
  - **Refs**: Lang (1999); Harvey–Lawson (1982).

- **`serre_gaga`** (`Hodge/Classical/GAGA.lean`)
  - **Meaning**: analytic subvarieties of projective manifolds are algebraic.
  - **Refs**: Serre (1956).

- **`harvey_lawson_fundamental_class`** (`Hodge/Kahler/Main.lean`)
  - **Meaning**: bridge between calibrated current limits and algebraic cohomology classes.
  - **Refs**: Harvey–Lawson (1982).

- **`omega_pow_algebraic`** (`Hodge/Kahler/Main.lean`)
  - **Meaning**: positive rational multiples of Kähler powers are algebraic.
  - **Refs**: Griffiths–Harris (1978).

- **`lefschetz_lift_signed_cycle`** (`Hodge/Kahler/Main.lean`)
  - **Meaning**: algebraicity is preserved under the Lefschetz correspondence.
  - **Refs**: Voisin (2002).

- **`flat_limit_existence`** (`Hodge/Kahler/Microstructure.lean`)
  - **Meaning**: Federer-Fleming compactness for integral currents.
  - **Refs**: Federer–Fleming (1960).

- **`calibration_defect_from_gluing`** (`Hodge/Kahler/Microstructure.lean`)
  - **Meaning**: bounded calibration defect for the microstructure gluing construction.
  - **Refs**: Federer–Fleming (1960).

- **`hard_lefschetz_bijective`** (`Hodge/Classical/Lefschetz.lean`)
  - **Meaning**: the Hard Lefschetz operator is a cohomology isomorphism.
  - **Refs**: Lefschetz (1924).

- **`barany_grinberg`** (`Hodge/Utils/BaranyGrinberg.lean`)
  - **Meaning**: discrepancy bound for vector sums (rounding lemma).
  - **Refs**: Bárány–Grinberg (1981).

- **`energy_minimizer`** (`Hodge/Analytic/Norms.lean`)
  - **Meaning**: existence of unique harmonic representative (energy minimizer).
  - **Refs**: Hodge (1941).

- **`polyhedral_boundary`** (`Hodge/Analytic/IntegralCurrents.lean`)
  - **Meaning**: boundary of integral polyhedral chain is polyhedral.
  - **Refs**: Federer–Fleming (1960).

- **`spine_theorem`** (`Hodge/Analytic/Calibration.lean`)
  - **Meaning**: calibration defect bound for currents with a calibrated part.
  - **Refs**: Harvey–Lawson (1982).

---

## Where the full axiom set is tracked

- **Full proof-chain list** (everything that still needs to be proved or classified):
  see `PROOF_CHAIN_AXIOMS.md`.
- **Opaque-elimination plan** (interface axioms to remove): see `AGENT_ASSIGNMENTS.md`
  and `REFACTORING_PLAN.md`.


