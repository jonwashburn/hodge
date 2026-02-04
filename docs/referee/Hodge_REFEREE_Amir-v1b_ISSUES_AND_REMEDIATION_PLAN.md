### Amir v1b referee packet → Lean formalization: issue inventory + remediation plan

**Source anchor**: `Hodge_REFEREE_Amir-v1b.tex` (referee-layer TeX, including notes like “Referee note: this is the quantitative bottleneck” and “Referee dependency checklist”).  
**Repo anchor**: `/Users/jonathanwashburn/Projects/hodge` (Lean 4 project).

This document has two goals:

- **(1) Identify what prevents the current Lean development from being an unconditional, Clay-standard formal proof** of the Hodge conjecture as stated in `Hodge/Main.lean`.
- **(2) Provide a concrete, staged plan** (with file-level targets and acceptance criteria) to resolve those issues.

> Important: `#print axioms ...` (via `Hodge/Utils/AuditAxioms.lean`) only reports *explicit* axioms in the proof term. It does **not** capture hidden assumptions introduced by `opaque` constants or “proof-first” placeholder definitions that trivialize the mathematics. Clay-standard readiness requires addressing both.

---

### Executive summary (where we're at)

**Progress update (2026-01-10)**: The following items have been completed:
- ✅ **Phase 0**: Audit infrastructure (`AuditAxioms.lean`, `AuditOpaque.lean`, `scripts/audit_faithfulness.sh`)
- ✅ **Phase 0**: All `opaque` constants replaced with `def := 0` stubs (auditable)
- ✅ **Phase 1A**: All `FundamentalClassSet_data_*` axioms converted to theorems (stub-level)
- ✅ **Phase 2A**: `ChartExtDeriv.lean` build break fixed
- ✅ **Phase 2C**: `sorry` blocks in `Advanced/*` eliminated or documented
- ✅ **Phase E**: `unitForm` is now the real constant-1 form (not 0)
- ✅ **Phase E**: `kahlerPow 0` wired to `unitForm`; `isRationalClass.unit` added
- 🚧 **Phase 2B** (in progress): Real exterior derivative infrastructure

**Current audit status** (`bash scripts/audit_faithfulness.sh`):
- ✅ No explicit axioms in `Hodge/`
- ✅ No `opaque` constants
- ✅ No `sorry` statements
- ⚠️ **3 semantic-stub blocker categories remain**:
  1. `extDerivLinearMap := 0` (exterior derivative)
  2. `FundamentalClassSet_data_impl := 0` (cycle class)
  3. `integration_current := 0` (integration current)
  4. Kähler/Hodge operators := 0 (hodge star, adjoint, laplacian)

---

**Original status (for reference)**:

- **Current Lean status**: The project builds and `AuditAxioms` can be made to report only core axioms (e.g. `propext`, `Classical.choice`, `Quot.sound`) depending on the current branch state; however **the proof path still relies on non-Clay-standard mechanisms**:
  - ~~**`opaque` black boxes** (e.g. `FundamentalClassSet_data_impl`, `integration_current`) that conceal missing constructions.~~ (Resolved: now `def := 0`)
  - ~~**Axiomatized properties of fundamental classes** (`FundamentalClassSet_data_isClosed`, `..._rational`, etc.).~~ (Resolved: converted to theorems)
  - **Placeholder/stub analytic operators** (e.g. `extDerivLinearMap := 0`, Kähler/Hodge operators `:= 0`) that collapse de Rham/Hodge theory to a degenerate model.
  - ~~**Isolated `sorry` blocks** in `Hodge/Analytic/Advanced/*` (not on the main proof path today, but they block an unconditional upgrade).~~ (Resolved: eliminated)

- **TeX v1b status**: The referee packet is structured around a “proof spine” with explicit bottlenecks. It highlights where the Lean formalization would have to do real quantitative work (notably the transport→flat-norm/gluing hinge, and the holomorphic complete-intersection upgrade with uniform \(C^1\) control).

- **Bottom line**: Even if we eliminate a short list of named Lean axioms, the proof is **not Clay-standard** until we remove `opaque` dependencies, replace placeholders with real definitions, and prove theorems (not assume interfaces) for the analytic/algebraic bridges.

---

### Issue inventory (Lean)

#### A. Explicit axioms and opaque constants on/near the main proof path

- **`Hodge/Classical/GAGA.lean`**
  - **`opaque FundamentalClassSet_data_impl`**: a black-box implementation behind `FundamentalClassSet_data`.
  - **Axioms about fundamental classes**:
    - `axiom FundamentalClassSet_data_isClosed ...`
    - `axiom FundamentalClassSet_data_empty ...`
    - `axiom FundamentalClassSet_data_is_p_p ...`
    - `axiom FundamentalClassSet_data_additive ...`
    - `axiom FundamentalClassSet_data_rational ...`
  - **Why this is blocking**: the proof uses `FundamentalClassSet_data` as the cycle class map / Poincaré dual of an algebraic subvariety. Clay-standard requires a *construction* and proofs of these properties from that construction, not axioms.

- **`Hodge/Analytic/Currents.lean`**
  - **`opaque integration_current`**: another hidden dependency for the current/form pairing story.
  - **Why this is blocking**: it prevents validating that “integration over a subvariety yields the fundamental class in de Rham cohomology”.

#### B. Placeholder definitions that trivialize the intended mathematics

- **Exterior derivative stub**
  - `Hodge/Analytic/Forms.lean`: `extDerivLinearMap := 0`, hence `smoothExtDeriv = 0`, hence many “closed/exact” facts become vacuous.
  - **Impact**: de Rham cohomology and Hodge-theoretic statements can collapse to a degenerate model unless carefully quarantined. Clay-standard requires replacing this with the real `d` and proving `d² = 0`, Leibniz, etc.

- **Hodge/Kähler operator stubs**
  - `Hodge/Kahler/Manifolds.lean`: `hodgeStar := 0`, `adjointDeriv := 0`, `laplacian := 0`, `lefschetzLambdaLinearMap := 0`.
  - **Impact**: “harmonic representative” and Kähler identities are not yet real; any Hard Lefschetz / Hodge decomposition built on these is not Clay-standard.

- **Misc stubs**
  - Several other files contain `toFun := 0` / “placeholder” maps that need to be audited for whether they affect the main proof chain.

#### C. “AuditAxioms” blind spots

- `Hodge/Utils/AuditAxioms.lean` prints explicit axioms of `hodge_conjecture_data`, but:
  - **Does not report** dependencies on `opaque` constants.
  - **Does not flag** placeholder definitions that make statements “true for the wrong reason”.

#### D. Advanced-module `sorry` (not currently on the main path, but blocks unconditional upgrade)

- `Hodge/Analytic/Advanced/LeibnizRule.lean`: `sorry` at ~213 and ~250.
- `Hodge/Analytic/Advanced/ContMDiffForms.lean`: commentary indicates additional `sorry`-level gaps.
- **Impact**: if the project’s roadmap is to upgrade from proof-first stubs to real differential geometry, these must be resolved.

#### E. Semantic stubs / “degenerate model” proofs (Clay-critical even when no axioms appear)

Even if the proof term contains no explicit `axiom`, Clay-standard requires that theorems are proved **for the intended definitions**, not because the definitions were replaced by placeholders that make statements vacuous.

- **Hard Lefschetz as a structure field (assumption, not a theorem)**
  - `Hodge/Cohomology/Basic.lean`: `KahlerManifold.lefschetz_bijective` (and related Lefschetz/Hodge-type fields) are carried as **typeclass fields**.
  - This is useful for “proof-first” scaffolding, but Clay-standard requires either:
    - proving Hard Lefschetz from Kähler/Hodge theory, or
    - exhibiting a concrete `KahlerManifold` instance in Mathlib’s framework that supplies these fields from proved theorems.

- **Kähler powers / wedge semantics**
  - `Hodge/Kahler/TypeDecomposition.lean`: `kahlerPow` currently uses placeholders (e.g. `ω^0` not implemented as the unit form; other branches/comments refer to “wedge := 0” regimes).
  - Any proof that depends on identities like \([\omega^p]\neq 0\), strict positivity, or hyperplane intersection normalization must be re-validated after upgrading these definitions.

- **Deep algebraicity/bridge theorems proved “because everything is zero”**
  - Some branches/iterations of `Hodge/Kahler/Main.lean` have had theorems like “\([\omega^p]\) is algebraic” and the Harvey–Lawson bridge proved by selecting the empty set and/or using lemmas like “rational classes imply zero,” which is only true under a degenerate rational/cohomology model.
  - Even if these are currently theorems (not axioms), they must be revisited once cohomology/fundamental class definitions are made real.

In short: **“no axioms listed” is not sufficient**. We also need **semantic faithfulness** of the mathematical objects.

---

### Issue inventory (TeX v1b → Lean implications)

The v1b referee layer includes explicit “what must be checked” notes. Two are especially important for Lean:

- **Quantitative bottleneck: transport ⇒ flat norm ⇒ gluing**
  - TeX: `\label{rem:lean-bottleneck-flatnorm}` (“Referee note: this is the quantitative bottleneck”) indicates exactly where Lean must eventually formalize quantitative bounds used downstream by gluing and almost-calibration.
  - Lean implication: to be Clay-standard, the corresponding Lean modules must implement:
    - the \(W_1\) / coupling estimates,
    - the homotopy/translation flat-norm bounds,
    - summation bookkeeping over a mesh,
    - and the resulting `prop:glue-gap`-style mass estimate for correction currents.

- **Sliver program: holomorphic complete-intersection upgrade with uniform \(C^1\) control**
  - TeX around the “sliver program” remarks notes the remaining hard step is the holomorphic upgrade with uniform control (Bergman kernel/jet surjectivity type inputs).
  - Lean implication: even if the proof spine is correct on paper, formalization requires either:
    - importing a substantial complex-analytic toolkit (Bergman kernels, Hörmander \( \bar\partial \)-solving, jet surjectivity), or
    - refactoring the proof to a route better supported by Mathlib.

Other notable TeX v1b flags:

- **Period locking hinge**: v1b includes an explicit “AI note” marking period locking as a hinge; formalization requires a clean integral-period basis and a rounding/budget argument consistent with torsion handling.
- **Parameter schedules & borderline cases**: the TeX dictionary and referee notes emphasize quantifier order and schedule constraints (e.g. \(p=n/2\) refinements). Lean needs those schedules as explicit inequalities with clear dependency packaging.

---

### Remediation plan (Clay-standard path)

This is a staged plan designed to keep the project building while progressively replacing placeholders/opaques/axioms with real constructions and proofs.

#### Phase 0 — Make “hidden assumptions” visible (1–2 weeks)

- **Add an “opaque audit”**:
  - New file: `Hodge/Utils/AuditOpaque.lean` (or a small script + CI check) that flags any `opaque` constants in the transitive dependency closure of `hodge_conjecture_data`.
  - Add `grep`-style CI checks for:
    - `^axiom` anywhere in `Hodge/` (except an explicitly whitelisted `Advanced/` sandbox),
    - `opaque` usage,
    - `extDerivLinearMap := 0` (or similar stubs) on the main path.

- **Define “Clay-standard acceptance criteria” for the repo**:
  - **No project-level axioms** on the main proof path.
  - **No `opaque`** on the main proof path (unless it is a definitional wrapper around a Mathlib constant whose theory is imported).
  - **No proof-first stubs** that trivialize intended content (e.g. `d := 0`).
  - Core Lean axioms like `propext` / `Classical.choice` are acceptable (Clay does not require constructivism), but should be explicitly documented.

#### Phase 1 — Replace `FundamentalClassSet_data` axioms with a real cycle class interface (1–2 months)

- **Goal**: remove `FundamentalClassSet_data_*` axioms by constructing `FundamentalClassSet_data` and proving:
  - closedness,
  - (p,p)-type (as needed),
  - additivity,
  - rationality / integral periods,
  - and compatibility with cup/wedge where used.

- **Implementation options**:
  - **Option A (preferred if Mathlib supports it)**: reuse Mathlib’s algebraic geometry + cycle class map (Chow groups / cohomology realization).
  - **Option B (minimal viable)**: define fundamental class via **integration current** and a de Rham comparison theorem; prove the needed properties.

- **Files likely involved**:
  - `Hodge/Classical/GAGA.lean` (replace axioms/opaque)
  - `Hodge/Analytic/Currents.lean` (replace `opaque integration_current`)
  - potentially a new `Hodge/Classical/CycleClass.lean`

#### Phase 2 — Replace `extDerivLinearMap := 0` with the real exterior derivative (2–6 months)

- **Goal**: migrate the “main path” to real differential forms and de Rham cohomology.
- **Approach**:
  - Adopt Mathlib’s `DifferentialForm` / manifold `extDeriv` if compatible with your existing `SmoothForm` API, or provide a compatibility layer.
  - Prove (or import) the basic lemmas currently used:
    - linearity,
    - `d² = 0`,
    - wedge Leibniz rule,
    - well-definedness of the cohomology quotient.

- **Deliverable**: `Hodge/Cohomology/Basic.lean` no longer depends on “d=0” semantics.

#### Phase 3 — Formalize the v1b “quantitative bottleneck” (transport ⇒ flat norm ⇒ glue) (3–12 months)

- **Goal**: replace the current proof-first placeholders in the microstructure/gluing chain by real inequalities and combinatorial bookkeeping.
- **Lean work items**:
  - Formal \(W_1\) coupling / KR duality interfaces used in the TeX.
  - Flat norm estimates under small translations/deformations.
  - Mesh summations with explicit schedules and quantified smallness.
  - The gluing correction estimate analogous to TeX `prop:glue-gap`.

- **Acceptance**: the Lean statement matching v1b’s “bottleneck” remark is proved without axioms/opaques.

#### Phase 4 — Cone geometry uniform interior radius (weeks to months; likely parallelizable)

- **Goal**: ensure that the cone definitions and “uniform interior radius” lemmas in `Hodge/Kahler/Cone.lean` are non-trivial and proved from:
  - pointwise strict positivity of \(\omega^p(x)\) in the strongly positive cone,
  - continuity of the cone data,
  - compactness of \(X\).

#### Phase 5 — Algebraicity of \([\omega^p]\) (months)

- **Goal**: formalize `lem:gamma-minus-alg` from v1b:
  - hyperplane sections / complete intersections,
  - Bertini-type generic smoothness,
  - identification of the cycle class with \(c_1(L)^p\).

#### Phase 6 — Harvey–Lawson / King / Chow/GAGA bridge (months to years)

- **Goal**: formalize “calibrated integral current ⇒ positive holomorphic chain ⇒ algebraic cycle” on projective manifolds.
- **Reality check**: Mathlib currently has limited GMT/current infrastructure; this phase may require substantial new library development.

#### Phase 7 — Remove “Kähler operators := 0” and prove Hodge theory/HLL (long horizon)

- **Goal**: upgrade Kähler/Hodge theory to the real setting:
  - real Hodge star, Laplacian, harmonic representative theorem,
  - Kähler identities,
  - Hard Lefschetz as a theorem rather than a structure field.

---

### Recommended parallelization (suggested agent ownership)

- **Fundamental class & cycle class map**: `Hodge/Classical/GAGA.lean`, `Hodge/Analytic/Currents.lean`
- **Exterior derivative / de Rham upgrade**: `Hodge/Analytic/Forms.lean`, `Hodge/Cohomology/Basic.lean`, plus the `Advanced/` modules
- **Quantitative bottleneck formalization**: transport/glue chain in `Hodge/Analytic/*` and `Hodge/Kahler/*`
- **Algebraicity of ω^p / intersection theory**: projective AG + hyperplane section route
- **HL/King/GAGA bridge**: calibrated currents → analytic cycles → algebraic cycles

---

### Concrete “done” checklist for Clay-standard readiness

- **No `axiom` in `Hodge/`** (except an explicitly quarantined `Advanced/` sandbox that is not imported by `Hodge/Main.lean`).
- **No `opaque` in the dependency closure of `Hodge/Main.lean`**.
- **No proof-first stubs** for `d`, cohomology, or fundamental classes on the main path.
- `lake build Hodge` succeeds.
- `lake env lean Hodge/Utils/AuditAxioms.lean` shows only acceptable core axioms (`propext`, `Classical.choice`, `Quot.sound`, etc.).
- A “semantic audit” document explains that the Lean objects coincide with their mathematical counterparts (not just typecheck under a degenerate model).

