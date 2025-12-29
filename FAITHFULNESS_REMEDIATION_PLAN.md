# Faithfulness Remediation Plan (Core Notions + Bridges)

Last updated: 2025-12-29

This document answers:
- **Which core notions/bridges are still axiomatized/opaque/stubbed (and therefore not yet faithful)?**
- **What is a concrete plan to make the formalization faithful**, while allowing “classical/accepted” theorems to remain as axioms?

The goal is **not** “0 axioms”. The goal is: **the objects and bridge statements mean what mathematicians mean** (e.g. de Rham cohomology is not trivial, “represents a class” is equality *in cohomology*, currents are not “all zero”, etc.), with any remaining axioms corresponding to standard theorems (Hard Lefschetz, GAGA/Chow, Harvey–Lawson, Federer–Fleming, Bergman asymptotics, …).

---

## 1. Current status: what is still not faithful?

Below are the *semantics-critical* items. If these remain as-is, the Lean theorem is not a faithful formalization (even if it compiles and has 0 `sorry`).

### 1.1 de Rham complex / cohomology is **vacuous**

File: `Hodge/Basic.lean`

- **Stub**: `IsExact` is defined as `True`.
- Therefore **`Cohomologous ω₁ ω₂` is always true**, because it is defined as `IsExact (ω₁ - ω₂)`.
- Therefore the quotient `DeRhamCohomologyClass` is **quotienting by a trivial relation** and carries no classical meaning.

Why this matters:
- Any later predicate like “rational cohomology class” can become **meaningless** if cohomology collapses.

Remedy target:
- Replace `IsExact := True` with a correct definition (or at minimum an **opaque predicate with nontrivial axioms**), and define cohomology from the de Rham complex.

### 1.2 Differential-form operators are **stubbed to 0**

File: `Hodge/Analytic/Forms.lean`

Definitions are currently stubs:
- `smoothExtDeriv` returns `0`
- `wedge` returns `0`
- `unitForm` returns `0`
- `hodgeStar`, `adjointDeriv`, `laplacian`, `lefschetzL`, `lefschetzLambda` return `0`

Why this matters:
- `omegaPow` (defined via `unitForm` and `wedge`) collapses.
- “closed”, “exact”, “primitive”, “harmonic”, etc. become vacuous or wrong.
- Any bridge to analytic/GMT content cannot be made faithful if `d` and `⋀` are not correct.

Remedy target:
- Replace stubs with actual definitions (preferably from Mathlib), or introduce an abstract de Rham complex API with axioms strong enough to make the development meaningful.

### 1.3 “Smooth forms” are not actually smooth; topology hacks

Files:
- `Hodge/Basic.lean`: `SmoothForm` is just a pointwise alternating map, with **no smoothness** condition.
- `Hodge/Analytic/Grassmannian.lean`: declares `TopologicalSpace (SmoothForm n X k) := ⊥` (discrete topology), making all “closure/interior/continuity” arguments meaningless.

Why this matters:
- Core analytic statements rely on *non-discrete* topology and actual smoothness.

Remedy target:
- Represent forms as **smooth sections** (e.g. `ContMDiff` sections) and remove the discrete-topology instance hacks.

### 1.4 Currents / mass / flat norm / integrality are **stubbed**

Files:
- `Hodge/Analytic/Currents.lean`: every `Current` evaluates to 0 (`toFun_zero`), `mass = 0`, `boundary = 0`, operations are constant-0.
- `Hodge/Analytic/IntegralCurrents.lean`: `isRectifiable := True`, `isIntegral` is “∃ set, True”, closure properties become trivial.
- `Hodge/Analytic/FlatNorm.lean`: `flatNorm := 0`.
- `Hodge/Analytic/Norms.lean`: `pointwiseComass := 0`, `L2Inner := 0`, `comass` is a discrete 0/1 gadget; `pointwiseInner` is `opaque`.

Why this matters:
- The whole GMT layer is currently “zero model”, so any “proof” using it is not the classical content.

Remedy target:
- Introduce a **nontrivial** current/GMT interface (even if many theorems remain axioms), so that:
  - `Current` is a genuine linear functional,
  - `boundary` is dual to `d`,
  - `mass`/`flatNorm` are genuine seminorms/norms,
  - “integral current” is not `True`.

### 1.5 Fundamental class / “represents class” lives at the wrong level (forms vs cohomology)

File: `Hodge/Classical/GAGA.lean`

Current situation:
- `FundamentalClass (W)` is defined as `0` (stub).
- `FundamentalClassSet` is `opaque` but returns a **form** `SmoothForm n X (2*p)`.
- `SignedAlgebraicCycle.RepresentsClass` is defined as **equality of forms**:
  - `Z.fundamentalClass p = η`.

Why this matters:
- Classically, the cycle class map is an element of **cohomology**.
- Equality of *chosen representatives as forms* is not canonical and not the right invariant.

Remedy target:
- Move representation predicates to cohomology:
  - define `cycleClass : ... → DeRhamCohomologyClass n X (2*p)` (or a dedicated cohomology type),
  - define `RepresentsClass` as equality **in cohomology**.

### 1.6 Non-classical “bridge axiom” currently proves the hard part

File: `Hodge/Kahler/Main.lean`

The proof of `hodge_conjecture'` currently uses:
- `cone_positive_represents` (axiom)

This axiom is **not** a standard classical theorem: it is essentially the target conclusion for the cone-positive case.

Remedy target:
- Replace `cone_positive_represents` by a theorem derived from the intended chain:
  - microstructure/Automatic SYR → calibrated limit → Harvey–Lawson → Chow/GAGA,
  - with all bridges stated at the cohomology level.

---

## 2. What can remain axioms (classical / accepted inputs)?

Assuming we fix the core notions above, it is reasonable to keep the following as axioms *initially*, since they are standard and/or currently far beyond Mathlib’s scope:

- **Hard Lefschetz** (`hard_lefschetz_bijective`)
- **Chow / GAGA** (`serre_gaga` or a Chow/GAGA interface)
- **Harvey–Lawson structure theorem** (`harvey_lawson_theorem`)
- **Federer–Fleming** compactness/deformation (`federer_fleming_compactness`, `deformation_theorem`)
- **Bergman kernel / peak sections** (Tian/Catlin/Zelditch-style asymptotics), `tian_convergence`
- **Serre vanishing**, `serre_vanishing`
- **Fixed-dimensional discrepancy rounding** (Bárány–Grinberg / Barvinok), `barany_grinberg`
- **Carathéodory**, **Wirtinger inequality**, etc.

Important: to be “acceptable”, these axioms must be stated in terms of **faithful objects** (real cohomology, real currents, real wedge/d, etc.), not on top of zero/trivial stubs.

---

## 3. Concrete remediation roadmap (phased)

### Phase 0 — Fix statement-level faithfulness (cheap, high leverage)

Goal: make “represents class” and “fundamental class” live in cohomology, not as raw form equality.

- **0.1** Introduce a cohomology-level cycle class map:
  - `cycleClassSet : (p : ℕ) → (Z : Set X) → DeRhamCohomologyClass n X (2*p)`
  - (or, better, a dedicated `CohomologyClass` type, see Phase 1)
- **0.2** Redefine:
  - `SignedAlgebraicCycle.RepresentsClass` as equality in cohomology:
    - `cycleClassSigned Z = DeRhamCohomologyClass.ofForm η`.
- **0.3** Update bridge axioms accordingly:
  - `cone_positive_represents`, `omega_pow_represents_multiple`, `lefschetz_lift_signed_cycle`
  - should talk about **cohomology equality**, not form equality.

Deliverable: the end theorem reads like the classical conjecture:
“there exists an algebraic cycle whose cohomology class equals the given class”.

### Phase 1 — Replace trivial de Rham cohomology with a nontrivial interface

Goal: remove `IsExact := True` and ensure de Rham cohomology is meaningful.

Two implementation options:

- **Option A (preferred)**: use Mathlib’s de Rham complex/cohomology for manifolds (if available for our manifold setup).
- **Option B**: introduce an **abstract de Rham complex API**:
  - `d : Ω^k → Ω^{k+1}` (opaque)
  - axioms: `d∘d = 0`, linearity, Leibniz with wedge, etc.
  - define `IsClosed`, `IsExact` nontrivially from `d`
  - define cohomology as the quotient `Z^k/B^k` (or an abstract type with axioms).

Deliverable: `DeRhamCohomologyClass` is no longer the quotient by a trivial relation.

### Phase 2 — Make “SmoothForm” actually smooth; remove discrete topology hacks

Goal: make `SmoothForm` represent genuine smooth differential forms.

- Replace the current `structure SmoothForm` with a type of **smooth sections** of the alternating-form bundle.
- Remove `TopologicalSpace (SmoothForm ...) := ⊥` and rebuild any parts that relied on it.

Deliverable: continuity arguments (Berge, compactness, etc.) at least become meaningful statements.

### Phase 3 — Fix Kähler metric / inner products / norms (still allowed to axiomatize deep analytic bounds)

Goal: have correct definitions of:
- pointwise inner product on forms
- comass norm
- L² inner product / energy

Keep as axioms if needed:
- Hodge theorem existence/uniqueness of harmonic representative,
- Sobolev/trace estimates (`trace_L2_control`), etc.

Deliverable: objects like `pointwiseInner`, `comass`, `L2Norm` have correct meaning.

### Phase 4 — Build a faithful GMT interface for currents (even if many theorems remain axioms)

Goal: replace the “zero model” with a structurally correct interface.

Minimum viable interface:
- `Current` as (continuous) linear functional on compactly supported smooth forms
- `boundary` defined as dual of `d`
- `mass`, `flatNorm` as seminorms/norms with correct axioms
- “integral current” not defined as `True`

Keep as axioms:
- Federer–Fleming compactness/deformation,
- evaluation estimates, lower semicontinuity, etc.

Deliverable: `automatic_syr` and the microstructure layer can be stated in the right vocabulary.

### Phase 5 — Algebraic geometry side: cycles and cycle class map

Goal: represent algebraic cycles and their cycle class in cohomology.

Practical path (given Mathlib gaps):
- Keep `IsAlgebraicSet` / `isAlgebraicSubvariety` as axioms/predicates initially.
- Add a *cohomological* cycle class map with functoriality/additivity axioms.
- Keep Chow/GAGA as an axiom connecting analytic ↔ algebraic.

Deliverable: “algebraic cycle represents cohomology class” becomes a correct statement.

### Phase 6 — Remove the non-classical bridge axiom(s) by proving the intended chain

Goal: eliminate the axiom `cone_positive_represents` (and any similar “hard part as axiom” shortcuts).

Strategy:
- Prove `cone_positive_represents` from:
  - microstructure (H1/H2) + compactness + calibration defect → calibrated limit,
  - Harvey–Lawson → analytic subvarieties,
  - Chow/GAGA → algebraic,
  - cycle class agreement in cohomology.

Deliverable: the Lean theorem is “unconditional modulo classical inputs”.

---

## 4. Agent-sized task breakdown (suggested)

If you want to distribute this work, here is a sensible first wave:

- **Agent A (Cohomology correctness)**:
  - Phase 1 Option B (abstract de Rham complex) OR wire in Mathlib’s de Rham cohomology.
  - Kill `IsExact := True` and remove triviality.

- **Agent B (Statement-level correctness)**:
  - Phase 0: move `RepresentsClass` / fundamental class to *cohomology-level*.
  - Update the bridge axioms in `Hodge/Kahler/Main.lean` and `Hodge/Classical/GAGA.lean`.

- **Agent C (Forms correctness)**:
  - Phase 2: refactor `SmoothForm` to actual smooth sections; remove discrete topology hacks.
  - Provide wedge/exterior derivative definitions (or interfaces).

- **Agent D (Currents/GMT interface)**:
  - Phase 4: replace the “zero current” model with a structurally correct interface.
  - Keep deep GMT theorems as axioms but fix the types/definitions.

- **Agent E (Algebraic cycle class interface)**:
  - Phase 5: define a cycle class map into cohomology and axiomatize its standard properties.
  - Make GAGA/Chow inputs compatible with those definitions.

---

## 5. Success criterion (“faithful modulo classical axioms”)

We can say “faithful modulo classical axioms” once:
- `SmoothForm`/`d`/`⋀`/cohomology are nontrivial and mathematically correct,
- “represents” is cohomology equality,
- the main non-classical bridge axiom `cone_positive_represents` is removed and replaced by the intended chain,
- any remaining axioms correspond to widely accepted theorems and are stated over the corrected core notions.

---

## 6. Immediate next steps (highest ROI)

If we want the fastest path to “not fake / not vacuous”, do these first:

1. **Kill the vacuity in `Hodge/Basic.lean`**: replace `IsExact := True` with a nontrivial definition (or opaque predicate + axioms) and rebuild `DeRhamCohomologyClass` accordingly.
2. **Move representation to cohomology**: redefine `SignedAlgebraicCycle.RepresentsClass` as equality in cohomology (not equality of forms), and update bridge axioms (`cone_positive_represents`, `omega_pow_represents_multiple_axiom`, `lefschetz_lift_signed_cycle`).
3. **Delete the discrete topology hacks**: remove `TopologicalSpace (SmoothForm ...) := ⊥` from `Hodge/Analytic/Grassmannian.lean` and adjust anything that relied on it.
4. **Replace “zero current model”**: refactor `Current` so it is not definitionally/equationally forced to be 0; keep deep GMT theorems as axioms, but make the interface structurally correct.
5. **Demote the non-classical shortcut**: eliminate `cone_positive_represents` as an axiom and replace it with a theorem that explicitly depends on the microstructure + Harvey–Lawson + GAGA chain (even if pieces of that chain remain axioms at first).


