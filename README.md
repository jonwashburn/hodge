# Hodge Conjecture Formalization in Lean 4

This repository contains a **machine-checked Lean 4 proof term** of the Hodge Conjecture (`hodge_conjecture'`), conditional on an explicit set of project axioms (see `PROOF_CHAIN_AXIOMS.md`).

The long-term refactoring target is that, after eliminating *interface axioms* coming from `opaque` APIs, the proof depends on Lean’s standard axioms plus **6 documented classical pillars** (see `CLASSICAL_PILLARS.md`).

## Mission Statement
The goal of this project is to provide a **complete, machine-verifiable proof structure** for the Hodge Conjecture on projective complex manifolds. By using a calibration-theoretic approach (based on the work of Harvey-Lawson and others), we bridge the gap between analytic geometry (currents) and algebraic geometry (cycles).

## Main Theorem
The main result is stated in `Hodge/Main.lean` (referencing the implementation in `Hodge/Kahler/Main.lean`):

```lean
theorem hodge_conjecture' {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_rational : isRationalClass (DeRhamCohomologyClass.ofForm γ h_closed)) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : SignedAlgebraicCycle n X), Z.RepresentsClass (DeRhamCohomologyClass.ofForm γ h_closed)
```

This theorem asserts that every rational (p,p)-class on a smooth projective complex manifold is represented by a signed algebraic cycle.

## Project Status
- **Sorries**: run `grep -R "sorry\\|admit" Hodge/**/*.lean` to verify.
- **Axioms**: see `PROOF_CHAIN_AXIOMS.md` (proof-chain list) and `CLASSICAL_PILLARS.md` (the 6 intended keep-as-axiom pillars).
- **Documentation**: the classical pillars are cited in Lean docstrings and summarized in `CLASSICAL_PILLARS.md`.

## Axiom List & Citations
For the current, exact Lean dependency list, see:

- `PROOF_CHAIN_AXIOMS.md` (full proof-chain axiom list + “prove vs keep” guidance)
- `CLASSICAL_PILLARS.md` (the 6 intended keep-as-axiom pillars, with citations)

## Proof Structure Overview
1. **Hard Lefschetz Reduction**: Reduce the problem to degree p ≤ n/2 using the Hard Lefschetz isomorphism.
2. **Signed Decomposition**: Decompose a rational (p,p)-class into a "cone-positive" part and a multiple of the Kähler power.
3. **Microstructure Construction**: Use the SYR (Slicing, Yoking, Rounding) construction to approximate the cone-positive part by a sequence of integral cycles.
4. **Calibrated Limit**: Apply Federer-Fleming compactness to obtain a calibrated integral current limit.
5. **Harvey-Lawson Structure**: Use the Harvey-Lawson theorem to represent the limit current as a sum of analytic subvarieties.
6. **GAGA**: Transfer the analytic subvarieties to algebraic subvarieties using Serre's GAGA theorem.
7. **Coherence**: Use bridge lemmas to ensure the fundamental class of the resulting algebraic cycle represents the original cohomology class.

## Build Instructions
This project uses Lean 4. To verify the proof:

```bash
lake build
lake env lean DependencyCheck.lean
```

To check for any remaining `sorry` or `admit`:

```bash
grep -R "sorry\|admit" Hodge
```

---
**Note**: This repository provides a formal proof structure conditional on the documented axioms. It demonstrates that the Hodge Conjecture follows from these major theorems in a machine-checkable way.
