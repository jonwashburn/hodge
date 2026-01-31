# Full-Unconditional Proof Completion Plan (No Stubs / No Axioms)

This document defines the **strong** completion criterion (“mathematically real; no gotchas”) and a dependency-ordered plan to reach it.

It is intentionally explicit about **what must be deleted/replaced**, because the current repo state compiles with **semantic scaffolding** (e.g. `:= 0`, `Prop := True`, `Set.univ`-support, `IsAnalyticSet`/`IsAlgebraicSet := IsClosed`, etc.).

## Completion Criterion (Strong / No Gotchas)

We are **done** only when all of the following hold:

- **No sorries**:
  - `grep -RIn --include="*.lean" -E '^[[:space:]]*sorry([^[:alnum:]_]|$)' Hodge/` finds none.
- **No custom axioms/opaque in proof-track `Hodge/`**:
  - `grep -RIn --include="*.lean" -E '^[[:space:]]*axiom\\b' Hodge/` finds none.
  - `grep -RIn --include="*.lean" -E '^[[:space:]]*opaque\\b' Hodge/` finds none.
- **No semantic stubs** (forbidden patterns in proof-track code):
  - No key maps/measure/integrals defined as `0` “to make things go through”.
  - No key properties defined as `True`.
  - No key geometric sets defined as `Set.univ` “as a placeholder”.
  - No “analytic/algebraic” redefinitions to “closed”.
  - No cycle class/fundamental class aliases that bypass integration/GMT.
- **Kernel axioms**:
  - `lake env lean Hodge/Utils/DependencyCheck.lean` reports only:
    - `propext`, `Classical.choice`, `Quot.sound`
  - No `sorryAx`, and no new axioms added.
- **Builds**:
  - Before any `lake build`: `lake exe cache get`
  - Prefer: `./scripts/build.sh`

## Baseline (What’s Broken Today)

Current audits show **no `sorry`**, but many **semantic placeholders** and a handful of **actual `axiom`/`opaque` declarations**.

### Actual axioms/opaque that must be eliminated

- `Hodge/Analytic/TestForms/LFTopology.lean`
  - `axiom realTopology : TopologicalSpace (TestForm n X k)`
- `Hodge/Analytic/TestForms/Operations.lean`
  - `axiom leibniz : True`
  - `axiom pullback_d ...`
- `Hodge/Analytic/Integration/SubmanifoldIntegral.lean`
  - `opaque submanifoldIntegral ...`
  - `axiom integral_add`, `axiom integral_smul`, `axiom integral_continuous`

### Key semantic stubs that must be replaced with genuine meaning

This is not exhaustive, but it captures the major blockers currently *on the proof spine*:

- **Test forms are a fake type**:
  - `Hodge/Analytic/TestForms/LFTopology.lean`: `structure TestForm ... where data : Unit := ()`
  - `TopologicalSpace (TestForm ...) := ⊥`
- **Operations on test forms are fake**:
  - `Hodge/Analytic/TestForms/Operations.lean`: `extDeriv`, `wedge`, `pullback` all return `⟨()⟩`.
- **Submanifold integration is fake / axiomatized**:
  - `Hodge/Analytic/Integration/SubmanifoldIntegral.lean`: `OrientedSubmanifold` is a placeholder; `submanifoldMeasure := Measure.count`; integral is `opaque` + axioms.
- **Current support is fake**:
  - `Hodge/Analytic/Currents.lean`: `Current.support := Set.univ` (explicitly documented as a placeholder).
- **Analytic & algebraic sets are approximated by closedness**:
  - `Hodge/Classical/HarveyLawson.lean`: `IsAnalyticSet` stores only `IsClosed`.
  - `Hodge/Classical/GAGA.lean`: `IsAlgebraicSet := IsClosed`.
- **Microstructure/SYR is fake**:
  - `Hodge/Kahler/Main.lean`: `AutomaticSYRData.universal` returns the **zero integral current** sequence.
  - `Hodge/Kahler/Microstructure.lean`: `CubulationExists.universal` is now a **genuine finite ball cover**
    with diameter control and chart containment (still needs real holomorphic sheets + gluing + defect → 0).
- **Hodge-theoretic operators are fake**:
  - `Hodge/Analytic/Norms.lean`: `HodgeStarData.trivial` defines ⋆ as `0`, etc.
  - `Hodge/Kahler/Identities/*.lean`: several operators are `:= 0`.
- **Poincaré dual / cycle class infrastructure is still an interface**:
  - `Hodge/Classical/CycleClass.lean`: `PoincareDualFormExists` is a typeclass interface; placeholder constructions exist (`omegaPower` etc.).

## Dependency Graph (High-Level)

The “real” proof needs the following layers in order:

1. **Real differential forms / test forms on manifolds** (LF topology, functoriality, operations).
2. **Real integration theory** (top-form integration and integration over oriented submanifolds, Stokes).
3. **Real GMT currents** (support, boundary, mass/comass, flat norm; integral currents).
4. **Real Kähler/Hodge theory operators** (⋆, Λ, Δ, Kähler identities as actually used).
5. **Real analytic geometry** (analytic sets = local holomorphic zero loci; regularity of calibrated currents).
6. **Real algebraic geometry + Chow/GAGA** (projective: analytic ⇒ algebraic).
7. **Cycle class / fundamental class** (integration current + PD + de Rham comparison).
8. **SYR microstructure construction** (actual sheets/cubulation/gluing; defect → 0).
9. **Federer–Fleming compactness + closure** (flat limit of cycles is cycle; existence of minimizers / compactness).
10. **Main theorem refactor**: `hodge_conjecture'` uses only real theory, no deep assumptions “injected” by stubs.

## Milestones (Concrete Lean Targets)

### M0 — Hygiene (avoid false positives in greps)

Some docstrings begin a line with the token `axiom` / `opaque`, which triggers repo audits even though it is not a declaration.
Fix by rewording those doc lines so the line does not start with `axiom`/`opaque`:

- `Hodge/Deep/Audit.lean` (doc line starting with “axiom dependencies …”)
- `Hodge/GMT/Mass.lean` (doc line starting with “opaque `comass` …”)

### M1 — Replace `TestForm` placeholder with real LF test forms on manifolds

Files:
- `Hodge/Analytic/TestForms/LFTopology.lean`
- `Hodge/Analytic/TestForms/Operations.lean`
- `Hodge/Analytic/Stage1/ManifoldTestFormsSkeleton.lean` (if still referenced)

Targets:
- Define `TestForm n X k` as a **real** space of compactly supported smooth form-valued functions with LF topology.
- Provide a real `TopologicalSpace`/`LocallyConvexSpace` structure (no `⊥`, no `axiom realTopology`).
- Define and prove:
  - `extDeriv` as actual exterior derivative
  - `wedge` as actual wedge product
  - `pullback` and `pullback_d`
  - Leibniz rule (real statement, not `True`)

### M2 — Replace axiomatized submanifold integral with real integration + Stokes

Files:
- `Hodge/Analytic/Integration/SubmanifoldIntegral.lean`
- `Hodge/Analytic/Integration/HausdorffMeasure.lean`
- `Hodge/Analytic/Integration/TopFormIntegral.lean`

Targets:
- Replace `OrientedSubmanifold` placeholder with a real structure (likely via Mathlib manifold/submanifold infrastructure).
- Define the induced measure (Hausdorff/volume) on the submanifold.
- Define `submanifoldIntegral` concretely (no `opaque`, no axioms).
- Prove linearity + continuity (in the real topology).
- Prove Stokes for appropriate classes (closed submanifolds, boundaries, etc.).

### M3 — Replace `Current.support := Set.univ` with genuine support

Files:
- `Hodge/Analytic/Currents.lean`

Targets:
- Define support via annihilation on test forms with disjoint support (standard GMT definition).
- Prove support is closed, and compatibility lemmas needed by HL/GAGA spine.

### M4 — Replace “analytic = closed” with real complex analytic sets

Files:
- `Hodge/Classical/HarveyLawson.lean`
- `Hodge/Deep/Pillars/HarveyLawson.lean` (deep track)

Targets:
- Redefine `IsAnalyticSet` as “locally the common zero locus of finitely many holomorphic functions” (or a Mathlib-available equivalent).
- Reprove closure lemmas (empty/univ/union/inter are *theorems*, not the definition).

### M5 — Replace “algebraic = closed” with real algebraic sets + prove Chow/GAGA

Files:
- `Hodge/Classical/GAGA.lean`
- `Hodge/Classical/ChowGAGA.lean`
- `Hodge/Deep/Pillars/GAGA.lean`

Targets:
- Redefine `IsAlgebraicSet` as Zariski-closed / polynomial zero-locus / scheme-theoretic closed subset (projective setting).
- Prove analytic ⇒ algebraic for projective manifolds (Chow + GAGA).

### M6 — Replace stubbed Hodge operators (⋆, Λ, Δ, etc.) with real ones

Files:
- `Hodge/Analytic/Norms.lean`
- `Hodge/Kahler/Identities/*.lean`
- any file using `hodgeStar`, `laplacian`, `adjointDeriv`, `lefschetzLambdaLinearMap` stubs

Targets:
- Implement pointwise inner product on forms from the Kähler metric.
- Implement Hodge star; prove its core algebraic properties.
- Implement the Kähler identities needed by the proof spine (as used in `Hodge/Cohomology/Basic.lean` etc.).

### M7 — Replace placeholder Poincaré dual / cycle class interface with real construction

Files:
- `Hodge/Classical/CycleClass.lean`
- `Hodge/Classical/GAGA.lean` (cycleClass integration bridges)

Targets:
- Define the integration current of an algebraic subvariety using real submanifold integration / rectifiability.
- Prove existence of a representing cohomology class (de Rham / PD) with the correct geometric characterization.
- Ensure `SignedAlgebraicCycle.cycleClass_geom` is **actually geometric**, not an alias.

### M8 — Replace microstructure/SYR universal stub with real construction

Files:
- `Hodge/Kahler/Microstructure.lean`
- `Hodge/Kahler/Main.lean`
- `Hodge/Deep/Pillars/Microstructure.lean`

Targets:
- Implement real cubulations/meshes from compactness + finite atlas, with actual mesh bounds.
- Implement holomorphic sheet construction and gluing estimates.
- Prove calibration defect → 0 and flat convergence.

### M9 — Implement Federer–Fleming / flat norm compactness “for real”

Files:
- `Hodge/Analytic/FlatNormReal.lean` (currently marked placeholder/off-track in comments)
- `Hodge/Deep/Pillars/FedererFleming.lean`

Targets:
- Define flat norm properly for the current model.
- Prove triangle inequality, lower semicontinuity, compactness, and “flat limit of cycles is cycle”.

### M10 — Final assembly: `hodge_conjecture'` without injected deep assumptions

Files:
- `Hodge/Kahler/Main.lean`
- any file that currently `letI`-injects `.universal`/stub data

Targets:
- Remove any stub `.universal` usage.
- Provide actual instances/proofs from the developed theory.
- Confirm `DependencyCheck` and greps pass unchanged.

## Working Rules (Enforced)

- Do not weaken theorem statements to make goals trivial.
- Do not “solve” by redefining key objects to `0`/`True`/`Set.univ`.
- If Mathlib lacks infrastructure, add it here as real theory (new files), not as axioms.

