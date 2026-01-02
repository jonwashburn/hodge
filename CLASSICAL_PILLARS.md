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

## Classical pillar axioms (target set = 6)

These six are explicitly marked in Lean with `STATUS: CLASSICAL PILLAR` (or
`STATUS: STRATEGY-CRITICAL CLASSICAL PILLAR`) in their docstrings.

- **`mass_lsc`** (`Hodge/Analytic/Calibration.lean`)
  - **Meaning**: lower semicontinuity of mass under flat-norm convergence:
    \(T_i \to T\) (flat) implies \(\mathrm{mass}(T) \le \liminf_i \mathrm{mass}(T_i)\).
  - **Why pillar**: requires the full “mass as a supremum over test forms + continuity”
    development for currents/flat topology.
  - **Refs**: Federer–Fleming (1960); Federer (1969).
  - **Used in**: the calibration/limit step of the microstructure pipeline.

- **`exists_uniform_interior_radius`** (`Hodge/Kahler/Cone.lean`)
  - **Meaning**: there exists a uniform radius \(r>0\) such that any form within
    pointwise comass-distance \(< r\) of \(\omega^p(x)\) lies in the strongly positive
    cone \(K_p(x)\), uniformly in \(x\).
  - **Why pillar**: packages deep Kähler-geometry positivity + compactness needed to get
    *uniform* control (a “cone has a uniform interior ball” statement over compact \(X\)).
  - **Refs**: Lang (1999); Harvey–Lawson (1982).
  - **Used in**: the cone-positivity shift lemma and related positivity arguments.

- **`serre_gaga`** (`Hodge/Classical/GAGA.lean`)
  - **Meaning**: GAGA/Chow: analytic subvarieties of a projective complex manifold are
    algebraic (with codimension preserved).
  - **Why pillar**: requires coherent sheaf theory + comparison theorems (big AG project).
  - **Refs**: Serre (1956); Hartshorne (App. B).
  - **Used in**: converting the Harvey–Lawson analytic output into algebraic cycles.

- **`harvey_lawson_fundamental_class`** (`Hodge/Kahler/Main.lean`)
  - **Meaning**: the “bridge” that the fundamental class of the Harvey–Lawson varieties
    represents the same de Rham cohomology class as the cone-positive input form.
  - **Why pillar**: packages deep GMT + de Rham/current comparison facts required for the
    proof strategy.
  - **Refs**: Harvey–Lawson (1982); Federer (1969); Demailly (2012).
  - **Used in**: the main cone-positive ⇒ algebraic-cycle representation theorem.

- **`omega_pow_represents_multiple`** (`Hodge/Kahler/Main.lean`)
  - **Meaning**: for \(c \in \mathbb{Q}_{>0}\), the class \(c\cdot[\omega^p]\) is algebraic
    (represented by a fundamental class of an algebraic subvariety).
  - **Why pillar**: needs intersection theory / cycle class machinery relating powers of
    the hyperplane class to algebraic cycles.
  - **Refs**: Griffiths–Harris (1978); Voisin (2002).
  - **Used in**: the “Kähler power” part of the signed decomposition step.

- **`lefschetz_lift_signed_cycle`** (`Hodge/Kahler/Main.lean`)
  - **Meaning**: Hard Lefschetz + algebraicity compatibility: when \(p>n/2\), the Lefschetz
    correspondence sends algebraic (signed) cycles to algebraic (signed) cycles.
  - **Why pillar**: requires the full Lefschetz/Λ infrastructure + cycle-class compatibility
    (deep Hodge theory + AG).
  - **Refs**: Voisin (2002); Griffiths–Harris (1978); Huybrechts (2005).
  - **Used in**: the high-degree reduction step of `hodge_conjecture'`.

---

## Where the full axiom set is tracked

- **Full proof-chain list** (everything that still needs to be proved or classified):
  see `PROOF_CHAIN_AXIOMS.md`.
- **Opaque-elimination plan** (interface axioms to remove): see `AGENT_ASSIGNMENTS.md`
  and `REFACTORING_PLAN.md`.


