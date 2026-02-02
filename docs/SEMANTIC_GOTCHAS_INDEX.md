# Semantic Gotchas Index (Proof-Track Blockers)

This file is a **living index** of remaining “no gotchas” blockers: definitions and instances that still trivialize the intended mathematics even though the repo currently compiles and the audits are green.

The intent is to make it easy for the integrator (and bounded agents) to find and eliminate semantic cheats without “passing the audit by changing the audit”.

---

## A. Cycle class / fundamental class

- **`SignedAlgebraicCycle.cycleClass_geom` is NOW CORRECT (Phase 7, 2026-02-01)**
  - Status: ✅ FIXED
  - Location: `Hodge/Classical/GAGA.lean:522-555`
  - Change: `cycleClass_geom` is now defined using `FundamentalClassSet(Z.support')`, NOT as `Z.cycleClass`.
  - The proof in `hodge_conjecture'` now uses `SpineBridgeData.fundamental_eq_representing` (not `rfl`).
  - **REMAINING**: The theorem `hodge_conjecture'` requires typeclass parameters:
    - `[CycleClass.PoincareDualFormExists n X p]` - Poincaré dual form existence
    - `[SpineBridgeData n X p]` - Bridge between geometric class and representing form
  - These encode **real mathematical content** that requires de Rham representability + Harvey-Lawson.

- **`FundamentalClassSet` requires `PoincareDualFormExists`**
  - Location: `Hodge/Classical/GAGA.lean:282-289` (`FundamentalClassSet`)
  - Location: `Hodge/Classical/CycleClass.lean:103-108` (`CycleClass.PoincareDualFormExists`)
  - Status: The interface is correct; no `.universal` stub exists.
  - **REMAINING**: Need to provide global instances by proving:
    1. De Rham representability theorem (every closed current is cohomologous to a smooth form)
    2. Harvey-Lawson bridge theorem (for calibrated currents, the form equals the calibration)
  - These are deep results not in Mathlib - would need to be built from scratch.

---

## A0. Foundational modeling gap: “forms live in the wrong fiber”

Even before integration/GAGA/HL, the current proof track’s differential-form model is not the real one:

- In `Hodge/Basic.lean`, `FiberAlt n k` is defined as a space of **ℝ-linear** alternating maps on `ℂⁿ`
  (viewed as a real vector space via `restrictScalars`).
  - Location: `Hodge/Basic.lean:50-55` (`TangentModel`, `FiberAlt`)
  With this choice, `FiberAlt n k` vanishes only for **k > 2n** (real dimension), which is consistent
  with the real de Rham grading on a complex n-fold (degrees \(0\) through \(2n\)).

This is why the repo can “talk about 2n-forms” while many constructions collapse.

**No-gotchas requirement**: the proof track must ultimately use a real de Rham model:
- forms are alternating **ℝ-multilinear** maps on the underlying real tangent (real dimension 2n),
  with coefficients in ℂ (or ℝ).

This change is deep and will require a staged migration (new `FiberAltR` / `SmoothFormR` layer + rewriting
`smoothExtDeriv`, wedge, norms, and all cohomology definitions).

---

## B. Submanifold integration / Stokes (deep GMT layer)

- **`SubmanifoldIntegration.universal` (the zero-measure/zero-integral model) has been removed**
  - Status: removed from `Hodge/Analytic/Integration/HausdorffMeasure.lean` (2026-02-01)
  - Remaining work: implement a mathematically correct integration/Stokes layer (and remove the remaining `integral := 0` stubs elsewhere).

- **`SubmanifoldIntegration.real` still has `integral := 0`**
  - Status: **removed** (2026-02-01)
  - Change: `Hodge/Deep/Pillars/Stokes.lean` no longer defines a Set-based `SubmanifoldIntegration.real`.
  - Current direction: data-based integration via `OrientedRectifiableSetData` / `ClosedSubmanifoldData`
    (see `Hodge/Analytic/Currents.lean`).

- **Obsolete integration/test-form scaffold stack removed**
  - The old LF “test forms” stack (`TestForm := Unit` and `submanifoldIntegral := 0`) was deleted:
    - `Hodge/Analytic/TestForms/LFTopology.lean` (deleted)
    - `Hodge/Analytic/TestForms/Operations.lean` (deleted)
    - `Hodge/Analytic/TestForms/CurrentsDual.lean` (deleted)
    - `Hodge/Analytic/Integration/SubmanifoldIntegral.lean` (deleted)
    - `Hodge/Analytic/Integration/IntegrationCurrent.lean` (deleted)
    - `Hodge/Analytic/Integration/Stokes.lean` (deleted)
  - This reduces semantic-noise in the repo and removes banned “everything is 0” proofs, but **does not** solve the real integration/Stokes pillar (which still requires replacing `SubmanifoldIntegration.real`).

- **Set-based integration plumbing removed from the currents layer**
  - Location: `Hodge/Analytic/Currents.lean`
  - Change: removed the entire legacy `setIntegral` / `ClosedSubmanifoldStokesData` / `StokesTheoremData` / `integration_current` tail.
  - Current direction: integration currents should be constructed from `ClosedSubmanifoldData` / `OrientedRectifiableSetData` via `...toIntegrationData.toCurrent`.

---

## C. SYR microstructure (deep construction)

- **Microstructure sequence is still the zero current (because no sheets are constructed)**
  - File: `Hodge/Kahler/Microstructure.lean`
    - `buildSheetsFromConePositive`: `sheets := ∅`, `support := ∅` (`:471-476`)
    - `microstructureSequence` evaluates by summing sheet integrals, hence is `0` with empty sheets (`:508-530`)
  - Note: `Hodge/Kahler/Microstructure/RealSpine.lean` still contains an older `zero_int`-based stub, but it is not currently imported by the proof spine.
  - Required fix: implement actual sheets + gluing + defect bound.

- **Sheet construction is still empty (support placeholder improved)**
  - File: `Hodge/Kahler/Microstructure.lean`
    - `buildSheetsFromConePositive`: `sheets := ∅` (still a semantic blocker)
    - `support := ∅` now (the former `support := Set.univ` placeholder was removed)
  - Required fix: nontrivial holomorphic sheet construction and support as the union of sheet carriers.

---

## D. Harvey–Lawson / King

- **`IsAnalyticSet` is semantic stub (closedness-only)**
  - Location: `Hodge/Classical/HarveyLawson.lean:38-41`
  - Current definition:
    ```lean
    class IsAnalyticSet ... (S : Set X) : Prop where
      isClosed : IsClosed S
    ```
  - **FORBIDDEN by playbook**: should be "local holomorphic zero locus"
  - Required fix: Define as sets locally defined by holomorphic functions
  - Blocked by: Need complex-analytic geometry infrastructure (not in Mathlib)

---

## E. Chow / GAGA

- **`IsAlgebraicSet` is semantic stub (closedness-only)**
  - Location: `Hodge/Classical/GAGA.lean:36-40`
  - Current definition:
    ```lean
    def IsAlgebraicSet ... (Z : Set X) : Prop :=
      IsClosed Z
    ```
  - **FORBIDDEN by playbook**: should be "polynomial zero locus" (Zariski-closed)
  - Required fix: Define as sets cut out by polynomial equations
  - Additionally need: Chow's theorem (analytic → algebraic on projective manifolds)

---

## F. Proof-track state: global instances and deep typeclasses

**Current state (2026-02-01)**:

- `hodge_conjecture'` DOES use deep typeclass parameters (NOT hidden):
  - `[CycleClass.PoincareDualFormExists n X p]` - explicit in signature
  - `[SpineBridgeData n X p]` - explicit in signature
  - These encode **real mathematical content** (de Rham representability + Harvey-Lawson bridge)
  - **No `.universal` instances exist for these** - intentionally kept as open requirements

- The spine is powered by global instances that use `.universal` constructors:
  - `instAutomaticSYRData` (backed by `AutomaticSYRData.universal`) in `Hodge/Kahler/Main.lean`
  - `instHarveyLawsonKingData` (backed by `HarveyLawsonKingData.universal`) in `Hodge/Classical/HarveyLawson.lean`
  - `instChowGAGAData` (backed by `ChowGAGAData.universal`) in `Hodge/Classical/GAGA.lean`
  - `instFlatLimitCycleData` (backed by `FlatLimitCycleData.universal`) in `Hodge/Classical/HarveyLawson.lean`

- The proof of `hodge_conjecture'` now uses `SpineBridgeData.fundamental_eq_representing` (NOT `rfl`):
  - `Hodge/Kahler/Main.lean:642` uses `SignedAlgebraicCycle.cycleClass_geom_eq_representingForm`

**What remains to eliminate deep typeclass binders**:
1. **De Rham representability**: Prove that closed currents are cohomologous to smooth forms. Requires: Sobolev spaces on manifolds, elliptic regularity, Hodge theory. NOT in Mathlib.
2. **Harvey-Lawson bridge**: Prove that for calibrated currents, the cycle class equals the calibration. Requires: GMT regularity theory. NOT in Mathlib.

These are **massive undertakings** that would require thousands of lines of new formalization.

---

## G. Recent real progress (not gotchas)

These are **real lemmas** that directly support the TeX spine around your current TeX location:

- `Hodge/GMT/TemplateExtension.lean`
  - `Hodge.TexSpine.Template.prefix_mismatch_decompose`
  - `Hodge.TexSpine.TemplateFlat.flatNorm_prefix_mismatch_le_unmatched`
- `Hodge/GMT/TransportFlat.lean`
  - `Hodge.TexSpine.TransportFlat.flatNorm_finSum_le_of_piecewise_decomp`
  - `Hodge.TexSpine.TransportFlat.flatNorm_mismatch_le_of_perm`

These are purely formal (no geometry cheated) and will be used when replacing the `zero_int` microstructure stub with real gluing.

- **Microstructure integration is now a genuine sheet-sum functional (removes the `setIntegral Set.univ` definitional gotcha)**
  - File: `Hodge/Kahler/Microstructure.lean`
    - `RawSheetSum.toIntegrationData` now sums `ClosedSubmanifoldData.toIntegrationData` over sheets (`:256-351`)
    - `microstructureSequence_eval_eq_integrate` rewrites evaluation to that functional (`:572-589`)
    - As a result, the microstructure layer no longer needs `[SubmanifoldIntegration n X]` in its core definitions.
  - Remaining blocker: `buildSheetsFromConePositive` is still empty (so the resulting current is still `0`).
