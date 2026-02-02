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

## H. Hodge theory / L2 integration

- **Basepoint L2 stub removed**
  - File: `Hodge/Analytic/Norms.lean`
  - `L2Inner` now depends on explicit `VolumeIntegrationData` (no basepoint/zero integration).
  - Cauchy–Schwarz is now an explicit interface (`L2InnerCauchySchwarzData`).
  - `Hodge/Analytic/Integration/L2Inner.lean` now provides
    `volumeIntegrationData_ofMeasure` (measure-based integration of continuous functions).
  - `Hodge/Analytic/Integration/VolumeForm.lean` provides
    `volumeIntegrationData_kahlerMeasure` (Kähler-measure wrapper).
  - Remaining: construct the *Kähler* volume measure + prove L2 properties and the ⋆–wedge relation.

- **Volume basis stub removed**
  - File: `Hodge/Analytic/Integration/VolumeForm.lean`
  - `volumeBasis` now depends on explicit `VolumeBasisData` (no zero-vector placeholder).

- **Placeholder `True` removed from cohomology representative lemma**
  - File: `Hodge/Analytic/Norms.lean`
  - `energy_minimizer_trivial` now states only the definitional existence of a representative.

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

## B1. Integral currents / polyhedral chains (GMT core)

- **Polyhedral chains are now an explicit data interface**
  - File: `Hodge/Analytic/IntegralCurrents.lean`
  - `IntegralPolyhedralChain'` now has a nontrivial generator:
    - `PolyhedralCurrentData` + constructor `ofPolyhedralData`.
  - This removes the (wrong) “all polyhedral chains are 0” consequence.
  - Remaining blocker: formalize actual simplicial/polyhedral geometry and
    prove Federer–Fleming approximation (no current instance yet).

---

## C. SYR microstructure (deep construction)

- **Sheet construction is now an explicit data interface (no empty-sheet stub)**
  - File: `Hodge/Kahler/Microstructure.lean`
    - `SheetConstructionData` provides the actual sheet construction.
    - `buildSheetsFromConePositive` now *requires* `SheetConstructionData` and no longer returns `∅` by definition.
    - The carrier is required to be the union of sheet supports (`support = sheetUnion`).
  - Remaining blocker: **implement real sheet construction + gluing/defect estimates** (TeX Proposition 4.3 / Theorem 4.1).

- **Real spine sequence is now an explicit data interface (no zero sequence stub)**
  - File: `Hodge/Kahler/Microstructure/RealSpine.lean`
    - `RealMicrostructureSequenceData` packages a concrete sequence with defect → 0.
    - `microstructureSequence_real` now depends on this data.

---

## D. Harvey–Lawson / King

- **`IsAnalyticSet` (closed + local holomorphic zero locus) is now real**
  - Status: ✅ FIXED
  - Location: `Hodge/AnalyticSets.lean` (`IsAnalyticSetZeroLocus`)
  - Integrated into the spine at: `Hodge/Classical/HarveyLawson.lean` (`IsAnalyticSet := IsAnalyticSetZeroLocus`)
  - Remaining deep blocker: **Harvey–Lawson regularity**
    (`CalibratedCurrentRegularityData.support_is_analytic_zero_locus`) is still an explicit typeclass binder.

---

## E. Chow / GAGA

- **`IsAlgebraicSet` (homogeneous polynomial zero loci pulled back from ℙ^N) is now real**
  - Status: ✅ FIXED
  - Location: `Hodge/Classical/AlgebraicSets.lean`
  - Used by: `Hodge/Classical/GAGA.lean` (algebraic subvarieties, closure lemmas, hyperplane/CI examples)
  - Remaining deep blocker: **Chow/GAGA theorem** itself (`ChowGAGAData`) is still an explicit typeclass binder.

---

## F. Proof-track state: global instances and deep typeclasses

**Current state (2026-02-02)**:

- `hodge_conjecture'` DOES use deep typeclass parameters (NOT hidden):
  - `[AutomaticSYRData n X]`
  - `[CycleClass.PoincareDualFormExists n X p]`
  - `[SpineBridgeData n X p]`
  - `[CalibratedCurrentRegularityData n X (2*(n-p))]`
  - `[HarveyLawsonKingData n X (2*(n-p))]`
  - `[ChowGAGAData n X]`
  - These encode **real mathematical content** (de Rham representability + Harvey-Lawson bridge)
  - **No `.universal` instances exist for these** - intentionally kept as open requirements

- `FlatLimitCycleData` is now treated as a proved infrastructure lemma (an `instance` exists),
  and it has been removed from the statement of `hodge_conjecture'` and its downstream theorems.

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
  - Remaining blocker: provide actual sheet constructions (no instance yet for `SheetConstructionData`).
