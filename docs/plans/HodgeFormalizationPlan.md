# Lean 4 Formalization Plan: Hodge Conjecture (Calibration-Coercivity)

This document serves as the persistent checklist for formalizing the "Calibration--Coercivity and the Hodge Conjecture" proof in Lean 4.

## I. Scaffolding & Topology (`Hodge/Basic.lean`)
- [x] Define `ProjectiveComplexManifold` structure.
- [x] Define `KahlerStructure` extending the above.
- [x] Define `HodgeClass (p : ℕ)` as the intersection of $H^{2p}(X, \mathbb{Q})$ and $H^{p,p}(X)$.
- [x] Define `AlgebraicCycle` and its fundamental class in cohomology.

## II. Cone Geometry & Positivity (`Hodge/Cone.lean`)
- [x] Define the `StronglyPositiveCone (p : ℕ)` at each point $x \in X$.
- [x] Define `IsConePositive (γ : HodgeClass p)`: existence of a smooth closed representative $\beta \in K_p$.
- [x] **Lemma (Kahler Power Positive)**: $\omega^p$ is in the interior of the cone.
- [x] **Axiom (Caratheodory Decomposition)**: Local structure of the cone.

## III. The Reductions (`Hodge/Reductions.lean`)
- [x] **Theorem (Hard Lefschetz Reduction)**: Reduce $p > n/2$ to $p \le n/2$ via hyperplane intersection.
- [x] **Lemma (Signed Decomposition)**: $\forall \gamma, \exists \gamma^+, \gamma^-$ such that $\gamma = \gamma^+ - \gamma^-$ and both are cone-positive.
- [x] **Lemma (Kahler Power Algebraic)**: $\gamma^-$ (multiples of $\omega^p$) is algebraic (Complete Intersection).

## IV. The Core Proof: SYR & Microstructure (`Hodge/SYR.lean`, `Hodge/Microstructure.lean`)
- [x] Define `IntegralCurrent` and `Mass`.
- [x] Define `CalibrationDefect (T : IntegralCurrent) (ψ : Form)`.
- [x] **The Spine Theorem**: If a sequence $T_k$ has vanishing defect, its limit is calibrated.
- [x] **Microstructure Realization**: Construction of $T_k$ from a cone-valued form $\beta$.
- [x] **Theorem (Automatic SYR)**: Automatic construction from cone-positive classes.

## V. External Axioms (The "Classical" Package)
- [x] `Axiom HarveyLawson`: Calibrated integral currents are analytic cycles.
- [x] `Axiom ChowGAGA`: Analytic subvarieties of projective space are algebraic.
- [x] `Axiom FedererFleming`: Compactness of integral currents.

## VI. Main Theorem Integration (`Hodge/Main.lean`)
- [x] **Theorem (Main Hodge)**: Every rational Hodge class is algebraic.
- [x] Compose the reductions, SYR limit, and classical axioms into the final proof.
- [x] Handle Hard Lefschetz case split and arithmetic closure.
- [x] Handle Hard Lefschetz case split and arithmetic closure.

## VII. Post-Novelty Cleanup (Filling Axioms)
- [x] Ground `IntegralCurrent` as a functional on forms in `SYR.lean`.
- [x] Link `HodgeClass` to rational cohomology in `Basic.lean`.
- [x] Replace `Axiom ChowGAGA` with a detailed analytic-to-algebraic interface in `Main.lean`.
- [x] Connect `AlgebraicCycle` fundamental class to Singular Homology.
- [x] Fill logical steps for Signed Decomposition and Spine Theorem.

