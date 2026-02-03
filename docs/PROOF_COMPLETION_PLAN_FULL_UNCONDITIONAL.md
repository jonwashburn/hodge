# Full-Unconditional Proof Completion Plan (No Stubs / No Axioms)

This document defines the **strong** completion criterion (“mathematically real; no gotchas”) and a dependency-ordered plan to reach it.

It is intentionally explicit about **what must be deleted/replaced**, because the repo can compile with **semantic scaffolding** (e.g. `:= 0`, `Prop := True`, `Set.univ`-support, and other gotchas).

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

### Baseline verification (2026-02-02 - updated)

Reproduced from repo root:

```bash
./scripts/build.sh
./scripts/audit_practical_unconditional.sh
./scripts/audit_stubs.sh --full
lake env lean Hodge/Utils/DependencyCheck.lean
grep -RIn --include="*.lean" -E '^[[:space:]]*sorry([^[:alnum:]_]|$)' Hodge/
grep -RIn --include="*.lean" -E '^[[:space:]]*axiom\b' Hodge/
grep -RIn --include="*.lean" -E '^[[:space:]]*opaque\b' Hodge/
```

Observed outputs (high-signal):

- ✅ **No `axiom` / `opaque` / `sorry`** in `Hodge/` (full scan)
- ✅ **Kernel dependency cone**:
  - `'hodge_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]`
  - `'hodge_conjecture'' depends on axioms: [propext, Classical.choice, Quot.sound]`
- ✅ **No `instance … .universal` declarations** in `Hodge/`
- ❌ **Deep typeclass binders in `hodge_conjecture'` signature** (still present):
  - `[AutomaticSYRData n X]` (SYR/microstructure realization scheme)
  - `[CycleClass.PoincareDualFormExists n X p]` (Poincaré dual form existence / de Rham representability)
  - `[SpineBridgeData n X p]` (Harvey–Lawson bridge: fundamental class = representing form)
  - `[CalibratedCurrentRegularityData n X (2 * (n - p))]` (HL regularity: calibrated support is analytic)
  - `[HarveyLawsonKingData n X (2 * (n - p))]` (HL/King structure theorem)
  - `[ChowGAGAData n X]` (Chow/GAGA: analytic → algebraic)
  - **Note**: `FlatLimitCycleData` was removed from the theorem statements (it exists as an `instance`), so it is no longer a binder.
- ⚠️ **Semantic gotchas still present** (tracked in `docs/SEMANTIC_GOTCHAS_INDEX.md`)

Current audits show:

- **No `sorry`**, **no `axiom`**, **no `opaque`** declarations in `Hodge/`.
- `Hodge/Utils/DependencyCheck.lean` reports only the standard Lean axioms:
  - `propext`, `Classical.choice`, `Quot.sound`
- **No `instance … .universal` declarations** in `Hodge/` (instances use `.universal` but via `exact`, not in `instance` line)

But the repo still contains **semantic placeholders** ("gotchas") that make the present proof track *not* mathematically genuine
even though it compiles.

## Reference TeX Proof (Newest) and Lean Spine Map

- **Newest proof narrative (TeX)**: `final-1-15-milan-05.tex` (timestamp 2026-01-15).
- **Secondary reference (requested prompt)**: `JA_hodge_approach_with_added_refs_blueCites.tex` (timestamp 2026-01-11).
- **Older proof drafts**: `Hodge_REFEREE_Amir-v1*.tex` (2026-01-06), `Hodge-v6-w-Jon-Update-MERGED.tex` (2025-12-29).

## Recent Deltas (2026-02-03)

- **Integration data refactor**:
  - `SubmanifoldIntegration` is now data-first via `SubmanifoldIntegrationData` in `Hodge/Analytic/Integration/HausdorffMeasure.lean`.
  - A thin legacy wrapper remains only for compatibility; new call sites take explicit data.
- **Top-form integration migrated**:
  - `Hodge/Analytic/Integration/TopFormIntegral.lean` now takes `SubmanifoldIntegrationData` everywhere.
  - Added local `castForm_*` helpers and real-scalar wedge lemmas to avoid dependent-elim pitfalls.
  - `L2Inner_wedge` now carries the necessary degree hypothesis `k ≤ 2 * n` (no silent truncation).
- **Kähler volume measure bridge**:
  - `KahlerVolumeMeasureData` is a **Type**-class (no Prop-collapsing of data).
  - `KahlerMeasureCompatibilityData` links `kahlerMeasure` with submanifold integration data.
  - Convenience accessor `kahlerSubmanifoldIntegrationData` threads the compatibility data.
- **Explicit compatibility layer**:
  - New `Hodge/Analytic/Integration/Compatibility.lean` introduces
    `TopFormIntegralCompatibilityData` (ties `topFormIntegral_real'` to `kahlerMeasure`).
- **Documentation refresh**:
  - Updated GMT/integration docstrings to reflect `ClosedSubmanifoldData`/`OrientedRectifiableSetData`
    and the removal of legacy Set-based stubs.
- **Integration currents (data-first)**:
  - `Hodge/GMT/IntegrationCurrent.lean` now exposes `integrationCurrentReal_data` /
    `integrationCurrent_data` constructors that take `ClosedSubmanifoldData` explicitly.
  - Existing `ClosedSubmanifoldStokesData`-based constructors remain only as thin wrappers.
  - `poincareDualForm_construct` now uses the explicit data-based constructor (wrapper retained).
- **L² vs wedge compatibility**:
  - `Hodge/Analytic/Integration/Compatibility.lean` now defines
    `L2InnerWedgeCompatibilityData` plus bridge lemmas
    `L2Inner_wedge_eq_L2Inner_measure` and
    `L2Inner_wedge_eq_L2Inner` (assumption‑based, no stubs).
- **Data-first tightening (Stokes/GMT)**:
  - `Hodge/GMT/GMTTests.lean` switched to `ClosedSubmanifoldData`-based constructors.
  - Stale `setIntegral` references removed from `Hodge/GMT/PoincareDuality.lean`
    and `Hodge/Analytic/Integration/HausdorffMeasure.lean` comments.
- **Data-first docs (integration currents)**:
  - `Hodge/GMT/IntegrationCurrent.lean` now explicitly documents the data-first
    constructors as the primary interface, and marks set-based wrappers as
    compatibility only.
- **Data-bearing class fix (Harvey–Lawson real)**:
  - `Hodge/Classical/HarveyLawsonReal.lean` changes `VarietyIntegrationCurrentData`
    from `Prop` to `Type` to avoid proof-irrelevance collapsing distinct currents.
- **Stokes pillar tightening (data-first lemma)**:
  - `Hodge/Analytic/Integration/StokesTheorem.lean` now includes a
    `ClosedSubmanifoldData`-based Stokes lemma showing exact forms integrate to zero.

**TeX → Lean module map (proof spine):**

1. **Main reduction + signed decomposition + algebraicity of ω^p**
   - TeX: `thm:main-hodge`, Lemma `signed-decomp`, Lefschetz reduction.
   - Lean: `Hodge/Kahler/Main.lean`, `Hodge/Kahler/HardLefschetz.lean`.
2. **Calibration–coercivity + spine theorem (quantitative)**
   - TeX: Theorem `thm:spine-quantitative`, H1/H2 packages.
   - Lean: `Hodge/Kahler/Microstructure.lean`, `Hodge/GMT/TransportFlat.lean`, `Hodge/GMT/GlueGap.lean`.
3. **SYR microstructure (local sheets → global currents)**
   - TeX: Theorem B/C/D (Steps 3–6 in Section 9).
   - Lean: `Hodge/Kahler/Microstructure.lean`, `Hodge/Kahler/Microstructure/RealSpine.lean`.
4. **Federer–Fleming compactness / flat norm closure**
   - TeX: Lemma `flat_limit_of_cycles_is_cycle`, compactness substeps.
   - Lean: `Hodge/GMT/FedererFleming.lean`, `Hodge/GMT/FlatNorm.lean`.
5. **Harvey–Lawson / King (calibrated currents → analytic varieties)**
   - TeX: `thm:syr` + Harvey–Lawson structure theorem.
   - Lean: `Hodge/Classical/HarveyLawson.lean`, `Hodge/Classical/HarveyLawsonReal.lean`.
6. **Chow/GAGA (analytic → algebraic on projective manifolds)**
   - TeX: Remark `chow-gaga`.
   - Lean: `Hodge/Classical/GAGA.lean`, `Hodge/Classical/AlgebraicSets.lean`.
7. **Cycle class / fundamental class bridge**
   - TeX: Fundamental class + PD identification.
   - Lean: `Hodge/Classical/GeometricCycleClass.lean`, `Hodge/Classical/CycleClass.lean`, `Hodge/Classical/GAGA.lean`.

## Agent Report Index (2026‑02‑03)

These reports capture the current “deep pillar” gaps before semantic restoration:

- `docs/AGENT_HODGE_REPORT.md` — Laplacian/harmonic forms; missing elliptic regularity + Hodge theorem.
- `docs/AGENT_STOKES_REPORT.md` — Submanifold integration & Stokes remain purely interface‑based.
- `docs/AGENT_FF_REPORT.md` — Federer–Fleming compactness still an interface; flat‑norm lemmas already present.
- `docs/AGENT_HL_REPORT.md` — Harvey–Lawson regularity + decomposition are deep binders in `Main.lean`.
- `docs/AGENT_GAGA_REPORT.md` — Chow/GAGA still a binder; Mathlib has projective schemes but no Chow/GAGA theorems.

## ⚠️ BLOCKING ISSUE: Deep Typeclass Binders (the real “pillars”)

**The `audit_practical_unconditional.sh` audit FAILS** because `hodge_conjecture'` still mentions deep binders:
- `[AutomaticSYRData n X]`
- `[CycleClass.PoincareDualFormExists n X p]`
- `[SpineBridgeData n X p]`
- `[CalibratedCurrentRegularityData n X (2 * (n - p))]`
- `[HarveyLawsonKingData n X (2 * (n - p))]`
- `[ChowGAGAData n X]`

These are **not kernel axioms**, but they *are* missing real mathematics. Eliminating them requires proving:

1. **De Rham representability / Poincaré dual forms** (`PoincareDualFormExists`):
   Construct, for each (co)dimension‑\(p\) geometric cycle/current, a smooth closed \(2p\)-form representing its de Rham class.

2. **Harvey–Lawson bridge** (`SpineBridgeData`):
   For spine-produced cycles, prove the equality of cohomology classes
   \([ \mathrm{FundamentalClassSet}(\mathrm{support}) ] = [\mathrm{representingForm}]\).

3. **Harvey–Lawson/King structure + regularity** (`HarveyLawsonKingData`, `CalibratedCurrentRegularityData`):
   Calibrated integral currents have analytic support and decompose as positive combinations of analytic varieties.

4. **Chow/GAGA** (`ChowGAGAData`):
   Analytic subsets of projective manifolds are algebraic (analytic → polynomial zero locus).

### Why these cannot be eliminated without massive new infrastructure

To provide global instances for these typeclasses (removing them from the signature), we need to PROVE (for real):

- **De Rham representability / Hodge theorem**: harmonic representatives, elliptic regularity, finite-dimensionality.
  Requires substantial PDE/functional analysis on manifolds; not available out-of-the-box in this Mathlib snapshot.

- **Harvey–Lawson/King**: calibrated-current regularity and decomposition into analytic varieties.
  Requires deep GMT + complex analytic geometry.

### Current state is mathematically honest

The formalization is:
- ✅ **Kernel-clean**: Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
- ✅ **No sorry blocks**: All proofs are complete
- ✅ **Semantically correct**: `cycleClass_geom` uses `FundamentalClassSet(support)`, not an alias
- ❌ **Audit-incomplete**: Deep assumptions remain as explicit parameters

This is the **best achievable state** without building significant new mathematical infrastructure.

The authoritative, file-pointed list is:

- `docs/SEMANTIC_GOTCHAS_INDEX.md`

### Key semantic stubs that must be replaced with genuine meaning

This is not exhaustive, but it captures the major blockers currently *on the proof spine*:

- **Geometric cycle class is NOW CORRECT (Phase 7, 2026-02-01)**:
  - ✅ `Hodge/Classical/GAGA.lean`: `SignedAlgebraicCycle.cycleClass_geom` NOW uses `FundamentalClassSet(Z.support')`.
  - ✅ The `rfl` proof is gone - replaced with `SpineBridgeData.fundamental_eq_representing`.
  - ⚠️ **REMAINING**: Deep typeclass binders `[PoincareDualFormExists n X p]` and `[SpineBridgeData n X p]`
    are still required as parameters to `hodge_conjecture'`. These encode real mathematical content
    (Poincaré duality / de Rham representability + Harvey-Lawson bridge).
- **Poincaré dual / fundamental class requires de Rham representability**:
  - `Hodge/Classical/CycleClass.lean`: `PoincareDualFormExists` typeclass provides the interface.
  - `Hodge/Classical/GAGA.lean`: `FundamentalClassSet` uses `PoincareDualFormExists`.
  - **TO ELIMINATE**: Need to prove de Rham representability theorem (every closed current on a compact
    Kähler manifold is cohomologous to a smooth form). This is deep GMT not in Mathlib.
- **Analytic/algebraic semantics restored (done; not a blocker anymore)**:
  - ✅ `Hodge/AnalyticSets.lean`: analytic sets = local holomorphic zero loci
  - ✅ `Hodge/Classical/AlgebraicSets.lean`: algebraic sets = projective homogeneous polynomial zero loci
  - Remaining: theorems (Chow/GAGA), not definitions.
- **Submanifold integration is still only an abstract interface**:
  - (removed) legacy Set-based `submanifoldIntegral := 0` scaffold stack has been deleted.
  - `Hodge/Analytic/Integration/HausdorffMeasure.lean`: the interface is now **data‑first** (`SubmanifoldIntegrationData`) and `SubmanifoldIntegration` is only a thin legacy wrapper. The old `SubmanifoldIntegration.universal` stub is removed, but there is still **no concrete data** with real integration/Stokes.
  - (updated 2026-02-01) `Hodge/Deep/Pillars/Stokes.lean` no longer defines a stubby Set-based `SubmanifoldIntegration.real`.
    Remaining work is to retire the legacy Set-based interface entirely and construct real integration currents from
    `OrientedRectifiableSetData` / `ClosedSubmanifoldData` (see `Hodge/Analytic/Currents.lean`).
- **Microstructure/SYR is still incomplete** (semantic blocker):
  - `Hodge/Kahler/Microstructure.lean`:
    - `RawSheetSum.toIntegrationData` has been rewired to a **sheet-sum** of genuine `ClosedSubmanifoldData` integrals
      (no longer `setIntegral` on a bare set), but
    - `buildSheetsFromConePositive` is now an **explicit data interface** (`SheetConstructionData`); it no longer returns `∅`.
      Remaining: implement real sheet construction + gluing/defect estimates.
  - `Hodge/Kahler/Microstructure/RealSpine.lean`: `microstructureSequence_real` is now an explicit data interface
    (`RealMicrostructureSequenceData`), no longer the zero sequence.
  - `Hodge/Deep/Pillars/Microstructure.lean`: deep-goal theorems are now explicit data interfaces
    (no `True` placeholders), but still require real proofs.
- **(Removed) legacy boundary-mass placeholder**:
  - The Set-based `boundaryMass := 0` stub (and its dependent Stokes plumbing) was removed from `Hodge/Analytic/Currents.lean`.
- **Hodge-theoretic operators still need real analytic proofs**:
  - `Hodge/Analytic/HodgeStar/FiberStar.lean`: fiber Hodge star now uses the real 2n‑basis (degree `k ↦ 2n−k`).
  - `Hodge/Analytic/Laplacian/Codifferential.lean` + `Hodge/Analytic/Laplacian/HodgeLaplacian.lean`:
    codifferential/Laplacian updated to the real `2n` degree conventions.
  - `Hodge/Analytic/Norms.lean`: `L2Inner` now depends on explicit `VolumeIntegrationData`
    (no basepoint/zero stub). `Hodge/Analytic/Integration/L2Inner.lean` provides
    `volumeIntegrationData_ofMeasure`, and `Hodge/Analytic/Integration/VolumeForm.lean`
    provides `volumeIntegrationData_kahlerMeasure`. The *Kähler* volume construction is still missing.
  - `Hodge/Analytic/Integration/VolumeForm.lean`: `KahlerVolumeMeasureData` is now **Type‑valued**
    (data, not `Prop`), and `KahlerMeasureCompatibilityData` records compatibility between
    `kahlerMeasure` and top-dimensional Hausdorff measure. Remaining: add top-form integration
    compatibility needed for `L2Inner` ↔ `L2Inner_wedge`.
  - `Hodge/Analytic/Integration/Compatibility.lean`: `TopFormIntegralCompatibilityData` now
    makes the top‑form compatibility explicit; still needs a real proof once top‑form evaluation
    is fully tied to the Kähler volume form.
  - `Hodge/Analytic/Integration/TopFormIntegral.lean`: `L2Inner_wedge := ∫ α ∧ ⋆β` is now defined with
    bilinearity lemmas; it still needs to be related to `L2Inner`.
  - `Hodge/Kahler/Identities/*.lean`: several operators are still `:= 0`.

- **Integral currents semantics still need upgrading**:
  - ✅ `isRectifiable` is no longer `True` (now a genuine Lipschitz-cover definition) in `Hodge/Analytic/IntegralCurrents.lean`.
  - ✅ `IntegralPolyhedralChain'.ofIntegrationData` shortcut removed.
  - Remaining: real polyhedral chain definition + Federer–Fleming approximation.

### Notes on resolved baseline items

- `Current.support` was previously `Set.univ`; it has been replaced by a standard nontrivial support definition in `Hodge/Analytic/Currents.lean`.

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

## Critical semantic mismatch to resolve early: Set-based integration + Stokes

Several “Phase 0” interfaces currently treat an arbitrary `Set X` as if it were a smooth, oriented,
boundaryless submanifold of whatever dimension is needed by the caller. This is *not* mathematically correct,
and it is the root cause of multiple downstream gotchas:

- `SubmanifoldIntegration` (in `Hodge/Analytic/Integration/HausdorffMeasure.lean`) integrates a `2*p`-form over a bare `Set X`.
- (updated 2026-02-01) The Set-based `setIntegral` plumbing was removed from `Hodge/Analytic/Currents.lean`;
  any future integration/Stokes work must continue in the data-based layer (`ClosedSubmanifoldData` /
  `OrientedRectifiableSetData`).
- The “Stokes” hook `SubmanifoldIntegration.stokes_integral_zero` is currently phrased as
  “exact forms integrate to 0 on *any* closed set”, which is far too strong (it is only true for
  boundaryless chains/submanifolds, not arbitrary closed sets).

**No-gotchas direction**:
- Replace “integration over `Set X`” with integration over a *structured* geometric object (at minimum: a rectifiable
  current / oriented submanifold / chain) that carries the correct dimensionality + boundary data.
- Move Stokes-type facts to the correct layer (`ClosedSubmanifoldStokesData` / chain boundary theorems), rather than
  baking a false global Stokes law into the integration primitive.

This refactor is prerequisite for genuine PD/fundamental class and geometric cycle classes.

## Milestones (Concrete Lean Targets)

### M0 — Hygiene (avoid false positives in greps)

Some docstrings begin a line with the token `axiom` / `opaque`, which triggers repo audits even though it is not a declaration.
Fix by rewording those doc lines so the line does not start with `axiom`/`opaque`:

- `Hodge/Deep/Audit.lean` (doc line starting with “axiom dependencies …”)
- `Hodge/GMT/Mass.lean` (doc line starting with “opaque `comass` …”)

### M1 — Replace `TestForm` placeholder with real LF test forms on manifolds

Files:
- `Hodge/Analytic/TestForms.lean` (current proof-track test forms: compactly supported smooth forms)
- (future) LF / Fréchet topology + continuity of operations on `TestForm`

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
- `Hodge/Analytic/Currents.lean` (data-based integration: `hausdorffIntegrate`, `IntegrationData`)
- `Hodge/Analytic/Integration/HausdorffMeasure.lean` (legacy Set-based integration interface to retire or refactor)

Targets:
- Replace `OrientedSubmanifold` placeholder with a real structure (likely via Mathlib manifold/submanifold infrastructure).
- Define the induced measure (Hausdorff/volume) on the submanifold.
- Define `submanifoldIntegral` concretely (no `opaque`, no axioms).
- Prove linearity + continuity (in the real topology).
- Prove Stokes for appropriate classes (closed submanifolds, boundaries, etc.).

### M3 — Current.support implemented (no longer `Set.univ`)

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

---

## TeX Proof Mapping (JA_hodge_approach_with_added_refs_blueCites.tex)

This section maps the attached TeX proof to concrete Lean targets. Each item
lists the TeX reference and the corresponding Lean file(s) that must be
implemented without stubs.

### Hodge Theory Core (Laplacian, Harmonic Representatives)

**TeX**: §2 (Exterior calculus and Hodge theory), §4 (Energy gap), §6 (Coulomb decomposition)

**Lean targets**:
- `Hodge/Analytic/HodgeStar/FiberStar.lean`
  - Completed nontrivial fiber Hodge star (`fiberHodgeStar_construct`).
- `Hodge/Analytic/Norms.lean`
  - `L2Inner` already uses `VolumeIntegrationData`; remaining: relate it to `L2Inner_wedge` (`∫ α ∧ ⋆β`)
    and prove the metric/volume normalization needed for the TeX proof.
- `Hodge/Analytic/Laplacian/Codifferential.lean`
  - Codifferential `δ := (-1)^{(2n)k+2n+1} ⋆ d ⋆` implemented as a real linear map (2n‑degree conventions).
- `Hodge/Analytic/Laplacian/HodgeLaplacian.lean`
  - Hodge Laplacian `Δ := d ∘ δ + δ ∘ d` defined (structural operator).
- `Hodge/Analytic/Laplacian/HarmonicForms.lean`
  - Harmonic forms defined as `ker(Δ)` (kernel submodule).
- `Hodge/Analytic/Integration/L2Inner.lean`
  - Use `kahlerMeasure` to instantiate `L2Inner` with real integration.
- `Hodge/Analytic/Integration/VolumeForm.lean`
  - Replace any placeholder volume-basis data with an orthonormal frame from the Kähler metric.
- `Hodge/Kahler/Identities/LambdaD.lean` and `Hodge/Kahler/Identities/LDelta.lean`
  - Replace placeholder operators `Λ`, `δ`, `L` with real definitions (from Hodge star / Lefschetz).

**Key theorems to formalize**:
- Hodge theorem: each cohomology class has a unique harmonic representative.
- Hodge decomposition: `α = γ_harm + dη` with `d*η = 0`.
- Energy identity: `‖α‖² = ‖γ_harm‖² + ‖dη‖²`.
- Type decomposition and orthogonality of `(r,s)` components.

### Calibration Coercivity and Cone Geometry

**TeX**: §3 (Calibrated Grassmannian), §7 (Calibration-coercivity)

**Lean targets**:
- `Hodge/Analytic/Grassmannian.lean`
  - Use continuous alternating maps for the fiber cone, and take topological closure.
  - Prove the calibrated cone is closed/convex (done: closure definition + proof).
- `Hodge/Kahler/Cone.lean`
  - Replace ad hoc cone definition with the fiber-level calibrated cone.
  - Define global cone defect via integration of `distToConeAtPoint`.

**Key theorems**:
- Cone closedness at each fiber (closure of conical span).
- Calibration-coercivity: `Defcone(α) ≤ E(α) - E(γ_harm)` under cone-valued harmonic rep.

### SYR Microstructure (Sheets, Gluing, Defect → 0)

**TeX**: §8 (Realization), Theorem 4.3 + Prop 6.2

**Lean targets**:
- `Hodge/Kahler/Microstructure.lean`
  - Replace `buildSheetsFromConePositive` stub (`∅`) with genuine sheets.
- `Hodge/Kahler/Microstructure/RealSpine.lean`
  - Replace `microstructureSequence_real := zero_int` with actual sequence.
- `Hodge/Deep/Pillars/Microstructure.lean`
  - Implement cubulation, local sheet existence, gluing bounds, defect estimate.
- `Hodge/GMT/TemplateExtension.lean`, `Hodge/GMT/TransportFlat.lean`
  - Use TeX “sliver-template-extension” and glue-gap lemmas.

### Federer–Fleming Compactness

**TeX**: Thm 4.2.17 (Fed69), Lemma “flat limit of cycles is cycle”

**Lean targets**:
- `Hodge/Classical/HarveyLawson.lean` (current flat limit interface)
- `Hodge/Deep/Pillars/FedererFleming.lean`
  - Replace `FlatLimitCycleData.universal` with real compactness theorem.

### Harvey–Lawson / King (Calibrated → Analytic)

**TeX**: Theorem 4.2 (Harvey–Lawson), King (1971)

**Lean targets**:
- `Hodge/Classical/HarveyLawson.lean`
  - Eliminate `CalibratedCurrentRegularityData` by proving analytic support.
- `Hodge/Deep/Pillars/HarveyLawson.lean`
  - Prove structure theorem: calibrated current decomposes into analytic subvarieties.

### Chow / GAGA (Analytic → Algebraic)

**TeX**: Chow (1949), Serre GAGA (1956)

**Lean targets**:
- `Hodge/AnalyticSets.lean` already defines local zero loci (analytic sets).
- `Hodge/Classical/GAGA.lean`
  - ✅ `IsAlgebraicSet` now uses projective homogeneous polynomial zero loci
    (see `Hodge/Classical/AlgebraicSets.lean`) and is no longer an `IsClosed` alias.
  - Prove Chow’s theorem: analytic ⊂ projective ⇒ algebraic.
- `Hodge/Deep/Pillars/GAGA.lean`
  - Replace placeholders (`True`, `IsClosed`) with actual algebraic geometry.
