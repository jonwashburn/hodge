# TeX Spine Unconditional Closure Plan (repeatable prompt)

## Status (2026-01-26) - MILESTONE ACHIEVED

**Kernel‑unconditional**: ✅ **ACHIEVED** (no `sorryAx`, no custom axioms).

**TeX‑faithful unconditional**: Partially achieved. See notes below.

Why: the repo still contains **semantic stubs/toy models** that make the TeX‑shaped statement go through
without the real GMT + algebraic geometry content (Dirac/basepoint “integration”, microstructure zero currents,
Harvey–Lawson “univ” placeholder, trivialized Chow/GAGA, etc.).

This plan is written so you can execute it **one step at a time** without confusing:
- “we introduced typeclasses/interfaces that *name* the missing theorems” (scaffolding), with
- “we proved the theorems / removed the toy models” (TeX‑faithful unconditional completion).

### Current theorem surface (today)

```lean
-- TeX-shaped (still assumes a deep bridge as a typeclass)
theorem hodge_conjecture {p : ℕ} [SpineBridgeData n X] ... :
    ∃ (Z : SignedAlgebraicCycle n X p), Z.cycleClass_geom = ofForm γ h_closed

-- Kernel-only (definitional shortcut)
theorem hodge_conjecture_kernel {p : ℕ} ... :
    ∃ (Z : SignedAlgebraicCycle n X p), Z.RepresentsClass (ofForm γ h_closed)
```

### Quick verification (kernel-unconditional only)

```bash
./scripts/build.sh
lake env lean Hodge/Utils/DependencyCheck.lean
grep -rnE "^\s*private axiom\b|^\s*axiom\b" Hodge --include="*.lean" || echo "(no axioms found)"
```

---

This is a **repeatable prompt for an AI coding agent** to make the Lean development **TeX‑faithful and unconditional**.

## Goal (what “unconditional” means here)

There are two notions of “unconditional” in this repo:

- **Kernel-unconditional**: `#print axioms hodge_conjecture'` shows no `sorryAx` / custom axioms (beyond classical axioms like `Classical.choice`).
- **TeX-faithful unconditional** (**this plan’s goal**): the proof is not “true by construction” because key objects are defined by **placeholders** (e.g. integrals/currents are `0`, cycle class is `ofForm representingForm`), but instead uses:
  - real integration currents,
  - real Stokes,
  - real compactness/glue-gap,
  - real Harvey–Lawson/King,
  - real Chow/GAGA,
  - and *only then* a geometric cycle class map with a proved spine bridge theorem.

This plan is about closing the gap from “kernel-clean” to “TeX-faithful”.

---

## Guardrails (repo rules)

- **CRITICAL**: never rebuild Mathlib from source.
  - Before any `lake build`, run:
    ```bash
    lake exe cache get
    ```
  - Prefer:
    ```bash
    ./scripts/build.sh
    ```
- Keep the repo building after every batch.
- Ground truth check:
  ```bash
  lake env lean Hodge/Utils/DependencyCheck.lean
  ```

---

## Ground-truth blockers on the current proof track (code-level facts)

These are the specific semantic shortcuts that must be removed for TeX-faithful unconditionality.

### 1) Microstructure uses **zero integration** and **zero currents**

File: `Hodge/Kahler/Microstructure.lean`

Key stubs (as of this plan):
- `topFormIntegral := fun _ => 0`
- `RawSheetSum.toIntegrationData.integrate := fun _ => 0`
- `RawSheetSum.toCycleIntegralCurrent` returns `zeroCycleCurrent …`

Quick confirm:
```bash
grep -nE "topFormIntegral.*fun _ => 0|integrate := fun _ => 0|zeroCycleCurrent" Hodge/Kahler/Microstructure.lean
```

**Why this blocks TeX-faithful completion**: SYR/gluing/defect bounds become vacuous because all integrals/currents are definitionally zero.

---

### 2) Harvey–Lawson uses a **dummy decomposition** and **zero integration current**

File: `Hodge/Classical/HarveyLawson.lean`

Key stubs:
- `integrationCurrentHL … := 0`
- `harveyLawsonSupportVariety.carrier := Set.univ`
- `harvey_lawson_theorem` returns the singleton `{Set.univ}` and “represents” is just `isCalibrated …`

Quick confirm:
```bash
grep -nE "integrationCurrentHL.*:=\\s*0|carrier := Set\\.univ|varieties := \\{harveyLawsonSupportVariety" Hodge/Classical/HarveyLawson.lean
```

**Why this blocks TeX-faithful completion**: the HL/King theorem is where the calibrated limit current becomes a genuine analytic cycle; right now it does not.

---

### 3) The cycle class is **defined** to be whatever form we carried (semantic cheat)

File: `Hodge/Classical/GAGA.lean`

Current proof-track definition:
- `SignedAlgebraicCycle.cycleClass := ofForm Z.representingForm Z.representingForm_closed`

Quick confirm:
```bash
grep -nE "def SignedAlgebraicCycle\\.cycleClass|:=\\s*ofForm Z\\.representingForm" Hodge/Classical/GAGA.lean
```

**Why this blocks TeX-faithful completion**: the main theorem becomes “true by construction” regardless of whether the algebraic sets `pos/neg` have anything to do with cohomology.

TeX requires: the cycle class be computed **from geometry** (fundamental class / integration current / PD form), and then proved equal to `[γ]`.

---

### 4) Stokes for `Set.univ` is still an unproved assumption (typeclass)

File: `Hodge/Analytic/Currents.lean`

Current situation:
- The old `private axiom stokes_property_univ_axiom` has been removed (good).
- Stokes is still not proved from real integration: it is packaged as a typeclass
  `StokesTheoremData n X k` and used to build `ClosedSubmanifoldStokesData.univ`.

Quick confirm:
```bash
grep -nE "class StokesTheoremData|theorem stokes_univ_set|ClosedSubmanifoldStokesData\\.univ" Hodge/Analytic/Currents.lean
```

**Why this blocks TeX-faithful completion**: Stokes must be proved from the real integration model,
not left as an assumed interface. In the end, the main theorem should not require Stokes as an extra
assumption beyond the manifold structure.

---

### 5) Poincaré dual / fundamental class infrastructure is still a placeholder

Files:
- `Hodge/Classical/CycleClass.lean` (placeholder PD form)
- `Hodge/Classical/GAGA.lean` / `Hodge/Classical/GAGA.lean` (fundamental class uses `CycleClass.poincareDualForm`)
- `Hodge/GMT/PoincareDuality.lean` (explicitly placeholder pipeline)
- `Hodge/Analytic/Integration/HausdorffMeasure.lean` (proxy integration model used by `integrateDegree2p`)

Quick confirm (spot checks):
```bash
grep -nE "poincareDualFormExists|hausdorffMeasure2p|basepoint" Hodge/Classical/CycleClass.lean
grep -nE "placeholder|returns 0" Hodge/GMT/PoincareDuality.lean
```

**Why this blocks TeX-faithful completion**: the “cycle class from geometry” requires a real PD/fundamental-class bridge.

---

### 6) GAGA/Chow is currently **trivialized**

File: `Hodge/Classical/GAGA.lean`

E.g. `serre_gaga` currently converts “analytic” to “algebraic” essentially by definitional/inductive bridging (not real AG).

Quick confirm:
```bash
grep -nE "theorem serre_gaga" -n Hodge/Classical/GAGA.lean
```

**Why this blocks TeX-faithful completion**: TeX uses deep AG (“analytic subvariety of projective ⇒ algebraic”); the current setup makes this tautological.

---

## The Unconditional (TeX-faithful) closure roadmap (ordered)

This matches the TeX spine: **SYR → glue-gap → realization-from-almost → HL/King → Chow/GAGA → geometric cycleClass → spine bridge → flip track**.

### Phase 0 — Baseline + safety rails (always do first)

- Run:
  ```bash
  ./scripts/build.sh
  lake env lean Hodge/Utils/DependencyCheck.lean
  ```
- Identify all “semantic stubs” on the proof track by searching for:
  - `fun _ => 0` in critical definitions,
  - `Set.univ` used as a “canonical variety”,
  - `cycleClass := ofForm representingForm`,
  - `private axiom` / `axiom`.

Definition of done for Phase 0:
- You have a concrete checklist of exact symbols to replace (not just “integration is stubbed somewhere”).

---

### Phase 1 — Real integration for top forms and submanifolds + real Stokes

**Objective**: replace the proxy integration used by `integrateDegree2p` / `setIntegral` with real measure-theoretic integration compatible with manifold structure.

Deliverables:
- A real `topFormIntegral` on `X` (compact, oriented) that is not definitionally zero.
- A real `setIntegral`/submanifold integral that can integrate pullbacks/restrictions of forms along (embedded) submanifolds or rectifiable sets.
- A **proved** Stokes theorem for:
  - `Set.univ` (closed manifold, empty boundary),
  - and the specific “sheet” domains used in microstructure.

Code changes (be concrete):
- `Hodge/Analytic/Integration/HausdorffMeasure.lean`
  - Replace `hausdorffMeasure2p` (currently `Measure.dirac basepoint`) with a real measure
    coming from a real metric/volume structure on `X`.
  - Replace `submanifoldIntegral` (currently “measure(Z) * ω(basepoint)(standardFrame)”) with an actual integral
    over `Z` of the restriction/pullback of ω.
  - Update `integrateDegree2p` so `setIntegral` is truly `∫_{x∈Z} ω`.
- `Hodge/Analytic/Currents.lean`
  - Ensure `setIntegral` uses the new real integration.
  - Replace the *assumed* Stokes interface (`StokesTheoremData`) by an actual theorem/instance derived from the
    real integration model (so Stokes is not an extra assumption).

Definition of done (hard checks):
- No basepoint/Dirac proxy integration remains:
  ```bash
  grep -rn "Measure.dirac basepoint" Hodge/Analytic/Integration/HausdorffMeasure.lean && exit 1
  grep -rn "standardFrame" Hodge/Analytic/Integration/HausdorffMeasure.lean && exit 1
  ```
- `setIntegral` is nontrivial and not based on point evaluation:
  ```bash
  grep -rn "basepoint" Hodge/Analytic/Integration/HausdorffMeasure.lean && exit 1
  ```

---

### Phase 2 — Make SYR microstructure currents real (no zero current regime)

**Objective**: rewrite `Hodge/Kahler/Microstructure.lean` so microstructure produces actual integration currents over sheets, with the correct mass/stokes properties.

Deliverables:
- `topFormIntegral` is real (uses Phase 1).
- `RawSheetSum.toIntegrationData.integrate` is a genuine integral (sum/integral over sheet union).
- `RawSheetSum.toCycleIntegralCurrent` returns a nontrivial current (not `zeroCycleCurrent`).
- Delete the “zero regime” lemmas that exist only to support stubs:
  - `RawSheetSum.toIntegralCurrent_toFun_eq_zero`,
  - `microstructureSequence_is_zero`,
  - any “proved because 0” bound lemmas.

Files/symbols to change (exact):
- `Hodge/Kahler/Microstructure.lean`
  - `SmoothForm.pairingData.integrate := fun _ => 0` (must become real top-form integration)
  - `RawSheetSum.toIntegrationData.integrate := fun _ => 0` (must become real `setIntegral` over `T_raw.support`)
  - `RawSheetSum.toCycleIntegralCurrent` (must construct from integration data, not `zeroCycleCurrent`)
  - remove or quarantine (tests only): `zeroCycleCurrent`, `zeroCycleCurrent_toFun_eq_zero`,
    `RawSheetSum.toIntegralCurrent_toFun_eq_zero`, `microstructureSequence_is_zero`

Acceptance checks:
```bash
grep -nE "integrate := fun _ => 0|zeroCycleCurrent" Hodge/Kahler/Microstructure.lean && exit 1
```

Definition of done:
- The microstructure sequence used by `automatic_syr` is not definitionally constant 0.
- Calibration defect estimates are non-vacuous and stated in TeX style.

---

### Phase 3 — Glue-gap / flat norm / compactness: make the GMT spine real

**Objective**: implement the real GMT results needed to pass from “almost cycles / bounded mass” to an actual limiting calibrated cycle.

Deliverables:
- Flat norm decomposition / isoperimetric filling / glue-gap estimate with mass control.
- Federer–Fleming compactness for the relevant class of currents.
- Theorems that are currently “true in the zero regime” must be re-proved for real currents.

Files/symbols to change (exact):
- `Hodge/GMT/GlueGap.lean`
  - Replace placeholder `currentMass` (currently `Classical.choose T.bound`) with a real mass definition
    that matches `Current.mass` (or prove a lemma relating them).
  - Replace interface typeclasses (`FlatNormDecompositionData`, `MicrostructureBoundaryData`,
    `IsoperimetricFillingData`) by actual theorems/instances derived from real GMT results.
- `Hodge/Analytic/FlatNorm.lean`
  - Ensure `flatNorm` is the genuine Federer–Fleming flat norm, and prove the decomposition/compactness lemmas
    needed by microstructure/glue-gap (not “by simp/trivial”).
- `Hodge/Classical/FedererFleming.lean`
  - Supply the compactness/deformation/approximation lemmas used to prove the flat norm decomposition.

Acceptance checks (minimum):
```bash
# No placeholder mass definition
grep -n "Classical.choose T.bound" Hodge/GMT/GlueGap.lean && exit 1

# These typeclasses should not be required by theorems on the main proof track
grep -rn "FlatNormDecompositionData\\|MicrostructureBoundaryData" Hodge/Kahler --include="*.lean" && exit 1
```

Definition of done:
- `microstructure_construction_core` produces a real sequence with a real convergence argument.

---

### Phase 4 — Harvey–Lawson/King: produce analytic cycles from calibrated limits

**Objective**: replace the placeholder HL theorem with the real structure theorem:
\[
T = \sum_i m_i [V_i]
\]
with analytic subvarieties \(V_i\) and positive integer multiplicities \(m_i\).

Deliverables:
- `integrationCurrentHL` is genuine integration current (not `0`).
- `harvey_lawson_theorem` produces actual analytic components (not `Set.univ`) and a real current equality statement (not just “represents := isCalibrated”).

Files/symbols to change (exact):
- `Hodge/Classical/HarveyLawson.lean`
  - Replace `integrationCurrentHL := 0`
  - Replace `harveyLawsonSupportVariety.carrier := Set.univ`
  - Replace the stub `harvey_lawson_theorem` output `{Set.univ}` with actual varieties/multiplicities + a current equality.
- `Hodge/Classical/HarveyLawsonReal.lean`
  - Implement `integrationCurrentOfVariety` (currently returns `0`)
  - Implement `weightedCurrentSum` (currently returns `0`)
  - Make `HarveyLawsonConclusion_real.current_eq` a real decomposition equality, not a placeholder.

Acceptance checks:
```bash
grep -nE "integrationCurrentHL.*:=\\s*0|carrier := Set\\.univ|varieties := \\{harveyLawsonSupportVariety" Hodge/Classical/HarveyLawson.lean && exit 1
grep -nE "def integrationCurrentOfVariety.*\\n.*:=\\s*0|def weightedCurrentSum.*\\n.*:=\\s*0" Hodge/Classical/HarveyLawsonReal.lean && exit 1
```

Definition of done:
- `harvey_lawson_represents` proves the real representation theorem in the sense of currents.

---

### Phase 5 — Chow/GAGA: analytic subvarieties of projective are algebraic (real AG)

**Objective**: replace the trivialized `serre_gaga` with a real theorem connecting complex-analytic subvarieties to algebraic subvarieties in projective geometry.

Deliverables:
- A nontrivial notion of “algebraic subvariety” (Zariski closed / scheme-theoretic).
- A proof (or imported Mathlib theorem) of Chow/GAGA appropriate for your setup.

Files/symbols to change (exact):
- `Hodge/Classical/GAGA.lean`
  - Replace the current “analytic ⇒ algebraic” bridge that is essentially definitional/inductive.
  - Make `AlgebraicSubvariety` mean what TeX means (Zariski closed / subscheme) and make codimension meaningful.
  - Rework `serre_gaga` so it is not a tautological constructor map.
- `Hodge/Classical/ChowGAGA.lean`
  - Delete/replace `instChowGAGAData_trivial`.
  - Provide a real `ChowGAGAData` instance backed by Mathlib algebraic geometry + complex analytic geometry.

Acceptance checks:
```bash
grep -n "instance instChowGAGAData_trivial" Hodge/Classical/ChowGAGA.lean && exit 1
grep -n "IsAnalyticSet_isAlgebraicSet" Hodge/Classical/GAGA.lean && exit 1
```

Definition of done:
- `serre_gaga` is no longer a definitional conversion.

---

### Phase 6 — Define cycle class geometrically and prove the spine bridge theorem

**Objective**: remove the definitional cheat `cycleClass := ofForm representingForm`.

Deliverables:
- A **geometric** cycle class map, e.g. from:
  - integration currents (fundamental class) + de Rham theorem / PD,
  - or a constructed PD form with proved properties.
- A proved theorem:
  \[
  \mathrm{cycleClass\_geom}(Z(\gamma)) = [\gamma]
  \]
  where \(Z(\gamma)\) is the cycle produced by the spine.

Files/symbols to change (exact):
- `Hodge/Classical/CycleClass.lean`
  - Replace the current “PD form exists” placeholder that branches on `basepoint ∈ Z`.
  - Eliminate dependence on `hausdorffMeasure2p := Measure.dirac basepoint`.
- `Hodge/GMT/PoincareDuality.lean`
  - Replace placeholder PD pipeline (`regularizeCurrentToForm`, etc.) with a real construction
    (or change the pipeline to avoid needing a PD *form* by working in current cohomology).
- `Hodge/Classical/GAGA.lean`
  - Make `FundamentalClassSet` a real fundamental class / integration-current-to-cohomology map.
  - Make `SignedAlgebraicCycle.cycleClass_geom` depend on that real fundamental class.
- `Hodge/Kahler/Main.lean` and `Hodge/Main.lean`
  - Remove `[SpineBridgeData n X]` from theorem signatures by proving the bridge theorem internally.

Acceptance checks:
```bash
# No “basepoint ∈ Z” PD form hack
grep -rn "basepoint" Hodge/Classical/CycleClass.lean && exit 1

# No bridge assumptions in the main theorem signatures
grep -n "SpineBridgeData" Hodge/Main.lean Hodge/Kahler/Main.lean && exit 1
```

Definition of done:
- `SignedAlgebraicCycle.cycleClass` is computed from geometry, not carried form.
- `hodge_conjecture'` is proved using the geometric class equality, not `rfl`.

---

### Phase 7 — Flip the proof track and delete stubs

**Objective**: once the real spine is complete, wire `Hodge/Kahler/Main.lean` to the real implementations and remove now-dead stub code.

Deliverables:
- `Hodge/Kahler/Main.lean` uses the real microstructure + HL + GAGA + geometric cycle class.
- Delete old stub definitions and any “proved because 0” lemmas.
- Run the ground truth check and ensure the theorem remains kernel-clean:
  ```bash
  lake env lean Hodge/Utils/DependencyCheck.lean
  ```

Concrete deletions/cleanups (examples — update as you go):
- `Hodge/Kahler/Microstructure.lean`
  - delete `zeroCycleCurrent*`, `microstructureSequence_is_zero`, and any “because 0” lemmas once real currents exist
- `Hodge/Classical/HarveyLawson.lean`
  - delete `harveyLawsonSupportVariety` / `{Set.univ}` fallback once real theorem exists
- `Hodge/Analytic/Integration/HausdorffMeasure.lean`
  - delete `basepoint`, `standardFrame`, and the Dirac‑based `hausdorffMeasure2p`
- `Hodge/Classical/GAGA.lean`
  - remove the kernel-only shortcut `SignedAlgebraicCycle.cycleClass := ofForm representingForm`
    (or clearly segregate it into an “archived/kernel-only” namespace and ensure TeX-faithful track doesn’t use it)

Final acceptance sweep (all must be empty):
```bash
grep -rn "Measure.dirac basepoint" Hodge --include="*.lean" && exit 1
grep -rnE "integrate := fun _ => 0|zeroCycleCurrent" Hodge --include="*.lean" && exit 1
grep -rnE "carrier := Set\\.univ|integrationCurrentHL.*:=\\s*0" Hodge --include="*.lean" && exit 1
grep -rn "SpineBridgeData" Hodge/Main.lean Hodge/Kahler/Main.lean && exit 1
./scripts/build.sh
lake env lean Hodge/Utils/DependencyCheck.lean
```

Definition of done:
- No proof-track definitions are “true by construction” via placeholder objects.
- The TeX spine is faithfully represented by real mathematical objects and theorems.

---

## “Prompt to the agent” (copy/paste)

> Implement TeX-faithful unconditional closure of `hodge_conjecture'`.  
> Do NOT use semantic stubs (e.g. `fun _ => 0` integrals/currents, `Set.univ` as dummy variety, `cycleClass := ofForm representingForm`).  
> Replace them with real integration currents, real Stokes, real GMT compactness/glue-gap, real Harvey–Lawson/King, and real Chow/GAGA.  
> Only after those are real, define `cycleClass` geometrically and prove the spine bridge theorem `cycleClass_geom(Z(γ)) = [γ]`.  
> Keep the repo building (`./scripts/build.sh`) and use `lake env lean Hodge/Utils/DependencyCheck.lean` as ground truth.  
> Before any `lake build`, run `lake exe cache get` (never rebuild Mathlib).  

