# Adversarial Audit / Proof-Risk Tracker

Last updated: 2025-12-29

This document is a **red-team checklist** for the repo. It records everything that could make the “proof” not a complete and correct proof **(even assuming the classical/standard mathematical theorems cited)**.

Scope:
- **Lean artifact**: what `hodge_conjecture'` *actually* proves, its axiom dependencies, and why it is **not yet** the classical Hodge conjecture.
- **TeX manuscript** `Hodge-v6-w-Jon-Update-MERGED.tex`: rigorous “referee-style” gap scan, with special focus on the novel **H1/H2 microstructure** packages (local holomorphic manufacturing + global coherence/gluing).

---

## Pass 1 — Lean statement vs classical Hodge (faithfulness audit)

### What Lean currently proves

`Hodge/Kahler/Main.lean`:
- `hodge_conjecture'` currently proves:
  - `∃ (Z : Set X), isAlgebraicSubvariety n X Z`
  - **but does not relate** `Z` back to the input class \([\gamma]\).

**Proof killer (statement mismatch):**
- There is **no** “fundamental class equals \([\gamma]\)” / `RepresentsClass`-style predicate in the conclusion.
- Therefore, even if the development is consistent, the Lean theorem is **weaker than the classical Hodge conjecture**.

### Exact axiom dependency set (auto-extracted)

Reproduce with:

```bash
lake env lean DependencyCheck.lean
```

Current output:

```
#print axioms hodge_conjecture'
'hodge_conjecture'' depends on axioms: [cohomologous_refl,
 cohomologous_symm,
 cohomologous_trans,
 exists_uniform_interior_radius,
 flat_limit_of_cycles_is_cycle,
 harvey_lawson_theorem,
 isRationalClass_add,
 isRationalClass_smul_rat,
 microstructureSequence_are_cycles,
 propext,
 serre_gaga,
 zero_is_pq,
 zero_is_rational_axiom,
 Classical.choice,
 Quot.sound]
```

### Repo-wide consistency checks (quick)

- **No `sorry` in `Hodge/**/*.lean`** (checked via grep).
- **Declared `axiom` count in `Hodge/**/*.lean`: 50** (checked via grep).

**Proof killer (stubbed/opaque core predicates):**
- Even apart from the weak conclusion, key predicates (e.g. rationality/type/algebraicity) are **opaque/stubbed**, so the Lean statement is not yet the classical conjecture “as mathematicians mean it”.

---

## Pass 2 — TeX closure chain (gluing + exact class + compactness)

Targeted areas audited and tightened:
- **Quantifier order / “\(o(m)\)” phrasing** around the gluing estimate and parameter schedule.
- **Flat-norm decomposition → vanishing-mass filling**: ensured “\(R\) is a boundary” is explicit.
- **Cohomology forcing step**: made integrality-of-periods usage explicit and clarified the torsion handling.
- **Compactness step**: ensured Federer–Fleming is the source of current convergence; Allard is varifolds only.

Key hidden hypothesis that was made explicit:
- In a projective setting, to use Hard Lefschetz over \(\mathbb Q\) and to assert \([\omega^p]\) is algebraic, we must fix \([\omega]=c_1(L)\in H^2(X,\mathbb Z)\) (or a positive multiple of restricted Fubini–Study).

---

## Pass 3 — H1/H2 microstructure package audit (highest risk)

This is the **main adversarial target**: H1/H2 are the novel, non-library components where a hidden false claim can invalidate the entire chain.

### H1: “local holomorphic multi-sheet manufacturing” risks

References (TeX):
- `Lemma \ref{lem:bergman-control}` (uniform \(C^1\) control on \(m^{-1/2}\)-balls)
- `Theorem \ref{thm:local-sheets}` (local multi-sheet construction)
- `Proposition \ref{prop:finite-template}` (realize a finite translation template locally)
- `Proposition \ref{prop:holomorphic-corner-exit-L1}` (corner-exit holomorphic slivers)
- `Proposition \ref{prop:corner-exit-template-net}` (robust template supply for a finite direction net)

#### Risk H1.1 — `lem:bergman-control` is a *deep external input*, not a proved lemma

`lem:bergman-control` is stated with a one-paragraph “standard consequence” proof and citations.
That is fine in a paper, but it must be treated as an **explicit external theorem input** (with a clearly stated hypothesis set) in any “no-gaps” claim.

Adversarial question:
- does the cited Bergman/peak-section machinery actually yield **uniform** gradient control for a prescribed jet with constants uniform in \(x\) and uniform over the finitely many charts used later?

#### Risk H1.2 — `thm:local-sheets` proof sketch contains potentially false “disjointness” heuristics

In the proof of `thm:local-sheets`, Substep 3.4 claims one can choose translations so that all affine planes are pairwise disjoint on a cube.

Adversarial concern:
- For \(p < n/2\), different complex \((n-p)\)-planes generically intersect (dimension count), so “pairwise disjoint across multiple direction families” is not automatically achievable without **localization/anchoring**.

Mitigation already present elsewhere in the manuscript:
- The corner-exit/vertex-anchoring route (`prop:holomorphic-corner-exit-L1` + `rem:vertex-star-coherence`) avoids this by working with **parallel translates of a single plane** per label and enforcing deterministic face incidence.

Action item:
- Ensure the H1 package points to the corner-exit template manufacturing as the real local engine (and treat the multi-direction local-sheets statement as either a derived corollary under extra hypotheses, or mark it as a nontrivial input).

#### Risk H1.4 — direction dictionary must be chosen inside a template-admissible dense open set

`prop:corner-exit-template-net` constructs an \(\varepsilon_h\)-net of directions **inside** a dense open subset \(\mathcal U\subset G_\C(n-p,n)\) where a “slanted-coordinate inequality” produces a corner-exit simplex template.

Adversarial concern:
- the proof must ensure the Carathéodory/dictionary approximation of \(\widehat\beta\) is compatible with restricting the dictionary to \(\mathcal U\).

Mitigation:
- since \(\mathcal U\) is dense and the net is chosen at scale \(\varepsilon_h\), this is plausible, but it should be stated explicitly wherever the dictionary is fixed.

#### Risk H1.3 — “generic perturbation preserves jets and \(C^1\) bounds” (Bertini step)

`prop:tangent-approx-full` uses:
- “small generic perturbation inside a linear system (which does not change jets at \(x\) nor the \(C^1\) estimates on the small ball)”

Adversarial concern:
- One must justify the existence of perturbations that both:
  - preserve the prescribed jet at \(x\), and
  - are sufficiently small in \(C^1\) on the relevant Bergman ball to keep the uniform gradient control.

This is plausible, but not automatic; it should be either:
- proved (quantitative section selection), or
- explicitly listed as an external quantitative Bertini/jet-stability input.

### H2: “global coherence and gluing” risks

References (TeX):
- `Proposition \ref{prop:global-coherence-all-labels}` (B1 packaged)
- `Corollary \ref{cor:global-flat-weighted}` and `Proposition \ref{prop:glue-gap}`
- `Proposition \ref{prop:cohomology-match}`

#### Risk H2.1 — simultaneous integer choices (budgets + slow variation + periods) may conflict

The package claims one can choose integer activations/counts simultaneously so that:
- local budgets match,
- slow variation holds across neighbors,
- global period constraints hold (via Bárány–Grinberg),
- and the face-edit regime remains \(O(h)\).

Adversarial concern:
- global “period-fixing” adjustments can, in principle, force large local changes unless one proves:
  - each individual contribution vector is uniformly tiny (mesh refinement),
  - and the correction scheme does not destroy slow-variation/prefix-edit bounds.

Mitigations in manuscript:
- bounded-correction absorption (`rem:bounded-corrections`)
- fixed dimension of constraints \(b=\mathrm{rank}\,H^{2n-2p}(X,\mathbb Z)\) (so discrepancy bounds are dimension-only)

Action item:
- explicitly track where the argument ensures “period rounding uses only bounded local modifications” (or else flag as an assumption).

#### Risk H2.2 — edge/corner contributions and “cycle on faces” assumptions

Many face-level bounds assume slice currents on interfaces are cycles / do not create edge terms.

Adversarial concern:
- in cubical decompositions, triple intersections and edges can contribute unless the construction forces deterministic incidence (corner-exit) and/or handles edge terms explicitly.

Mitigation:
- the corner-exit mechanism is designed to control which faces are hit (G1-iff) and to keep unmatched tails small.

Action item:
- ensure every place using “\(B_F^{un}\) is a cycle” explicitly accounts for possible edge terms (either by construction or separate lemma).

---

## Tracking: immediate "proof blockers"

These are the *highest-leverage* blockers to a "complete and true proof" claim.

1. **Lean statement too weak**: no representation of \([\gamma]\) by the produced algebraic object.
2. **Lean uses many axioms/opaque predicates**: current artifact is not the classical conjecture.
3. **H1 relies on deep Bergman/jet control**: must be treated as explicit external theorem input.
4. **Local multi-direction disjointness (as written) is suspect** unless replaced by corner-exit anchoring logic.
5. **H2 simultaneous rounding**: must ensure period-fixing does not break slow-variation/face-edit bounds.

---

## Remediation Log

### 2025-12-29: Statement Strengthening

**Issue addressed**: The main theorem `hodge_conjecture'` was too weak - it only asserted existence of an algebraic variety, not that it *represents* the input class \([\gamma]\).

**Remediation**:

1. **Added `RepresentsClass` predicate** to `SignedAlgebraicCycle`:
   ```lean
   def SignedAlgebraicCycle.RepresentsClass {p : ℕ} (Z : SignedAlgebraicCycle n X) (η : SmoothForm n X (2 * p)) : Prop :=
     Z.fundamentalClass p = η
   ```

2. **Strengthened `hodge_conjecture'`** to return a signed algebraic cycle that *represents* the input class:
   ```lean
   theorem hodge_conjecture' {p : ℕ} (γ : SmoothForm n X (2 * p))
       (h_rational : isRationalClass (DeRhamCohomologyClass.ofForm γ)) (h_p_p : isPPForm' n X p γ) :
       ∃ (Z : SignedAlgebraicCycle n X), Z.RepresentsClass γ
   ```

3. **Added `SignedDecomposition` structure** that tracks the decomposition \(γ = γ^+ - γ^-\) and carries the proof that \(γ^- = N \cdot ω^p\):
   - This allows us to actually construct a signed cycle whose fundamental class equals \(γ\).

4. **Added axioms for fundamental class representation**:
   - `cone_positive_represents`: a cone-positive form is represented by an algebraic variety
   - `omega_pow_represents_multiple`: a rational multiple of \(ω^p\) is represented by a complete intersection
   - `harvey_lawson_fundamental_class`: Harvey-Lawson theorem produces varieties whose fundamental class equals the input
   - `lefschetz_lift_signed_cycle`: Hard Lefschetz lift preserves representation

**Current status**: The Lean theorem now asserts the correct statement (existence of a representing signed algebraic cycle), but relies on these additional axioms to bridge currents ↔ algebraic geometry.

### Remaining work for faithfulness

The following are still required for a faithful formalization:

1. **Prove or axiomatize** `FundamentalClassSet` to be a non-trivial map (currently stubbed to 0).
2. **Make `isRationalClass` non-trivial** (currently opaque predicate).
3. **Make `isPQForm` non-trivial** (currently opaque predicate).
4. **Make `IsAlgebraicSet` non-trivial** (currently opaque predicate).
5. **Define `DeRhamCohomologyClass` as a true quotient** (partially done - now uses `Quotient`, but cohomologous relation is axiomatized).


