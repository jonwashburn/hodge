# Semantic Gotchas Index (Proof-Track Blockers)

This file is a **living index** of remaining “no gotchas” blockers: definitions and instances that still trivialize the intended mathematics even though the repo currently compiles and the audits are green.

The intent is to make it easy for the integrator (and bounded agents) to find and eliminate semantic cheats without “passing the audit by changing the audit”.

---

## A. Cycle class / fundamental class

- **`SignedAlgebraicCycle.cycleClass_geom_data` is NOW CORRECT (Phase 7, 2026-02-01)**
  - Status: ✅ FIXED
  - Location: `Hodge/Classical/GAGA.lean:522-555`
  - Change: `cycleClass_geom_data` is defined using `FundamentalClassSet_data(support_data)`, NOT as `Z.cycleClass`.
  - The proof spine uses `SpineBridgeData_data` (data‑first), not `rfl`.
  - **REMAINING**: The theorem `hodge_conjecture'` requires typeclass parameters:
    - `[CycleClass.PoincareDualFormFromCurrentData n X p]` - Poincaré dual form from integration current
    - `[SpineBridgeData_data n X]` - Bridge between geometric class and representing form
  - These encode **real mathematical content** that requires de Rham representability + Harvey-Lawson.

- **`FundamentalClassSet_data` requires `PoincareDualFormFromCurrentData`**
  - Location: `Hodge/Classical/GAGA.lean:337-370` (`FundamentalClassSet_data`)
  - Location: `Hodge/Classical/CycleClass.lean:330-410` (`CycleClass.PoincareDualFormFromCurrentData`)
  - Status: The interface is correct; no `.universal` stub exists.
  - `PoincareDualFormData` no longer carries stub fields (`nonzero_possible`, `geometric_characterization`).
  - **Data-first update**: `poincareDualForm_data` is **definitionally** the regularization of
    `integrationCurrent_data`. The set-based `PoincareDualFormExists` remains only as a compatibility wrapper.
  - **Subvariety data-first bridge**: analytic/algebraic subvarieties now have
    explicit interfaces (`AnalyticSubvarietyClosedSubmanifoldData`,
    `AlgebraicSubvarietyClosedSubmanifoldData`) producing `ClosedSubmanifoldData`.
  - **Signed cycle support data**: `SignedAlgebraicCycleSupportData` provides
    `ClosedSubmanifoldData` for the support of a signed algebraic cycle, enabling
    data‑first `cycleClass_geom_data` and `SpineBridgeData_data`.
  - **REMAINING**: Need to provide global instances by proving:
    1. De Rham representability theorem (every closed current is cohomologous to a smooth form)
    2. Harvey-Lawson bridge theorem (for calibrated currents, the form equals the calibration)
  - These are deep results not in Mathlib - would need to be built from scratch.
- **`PoincareDualFormExists` (set‑based) still uses a Kähler‑power placeholder**
  - Location: `Hodge/Classical/CycleClass.lean:140-210` (`omegaPower` + `poincareDualFormData_of_set`)
  - Status: Compatibility‑only; not used on the data‑first proof spine.
  - **REMAINING**: Replace with real integration-current construction and de Rham representability.
  - **Note**: the data-first PD interface still awaits a real construction; it simply
    moves the assumption to explicit `ClosedSubmanifoldData`.

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
    `volumeIntegrationData_kahlerMeasure` (Kähler-measure wrapper); finiteness now
    comes from `KahlerVolumeMeasureData.finite` (explicit data).
  - Remaining: construct the *Kähler* volume measure + prove L2 properties and the ⋆–wedge relation.
  - `KahlerMetricData.trivial` removed (no zero inner-product placeholder).
  - Removed the tautological `kahlerMeasure_finite` lemma; finiteness is now an explicit
    assumption for `volumeIntegrationData_kahlerMeasure`.

- **Hodge Laplacian / harmonic forms definitions added**
  - Files: `Hodge/Analytic/Laplacian/HodgeLaplacian.lean`,
    `Hodge/Analytic/Laplacian/HarmonicForms.lean`
  - Added structural definition `Δ := d ∘ δ + δ ∘ d` and kernel-based harmonic submodule.
  - Remaining: elliptic regularity + finite-dimensionality + Hodge decomposition theorems.

- **Volume basis stub removed**
  - File: `Hodge/Analytic/Integration/VolumeForm.lean`
  - `volumeBasis` now depends on explicit `VolumeBasisData` (no zero-vector placeholder).

- **Placeholder `True` removed from cohomology representative lemma**
  - File: `Hodge/Analytic/Norms.lean`
  - `energy_minimizer_trivial` now states only the definitional existence of a representative.

- **Kähler identity placeholder operators removed**
  - Files: `Hodge/Kahler/Identities/LambdaD.lean`, `Hodge/Kahler/Identities/LDelta.lean`
  - Replaced `:= 0` operators with explicit data interfaces
    (`KahlerIdentityLambdaDData`, `KahlerIdentityLDeltaData`).

- **Cohomology pairing stub removed**
  - File: `Hodge/Analytic/Integration/PairingConnection.lean`
  - `pairingCohomology` now depends on explicit `CohomologyPairingData`
    instead of returning `0`.
  - Remaining: provide a genuine pairing via Stokes + Poincaré duality.

- **Cohomology integral stub removed**
  - File: `Hodge/Analytic/Integration/StokesTheorem.lean`
  - `cohomologyIntegral` now depends on explicit `CohomologyIntegralData`
    instead of returning `0`.

- **Kähler volume measure data is now real data (not Prop)**
  - File: `Hodge/Analytic/Integration/VolumeForm.lean`
  - `KahlerVolumeMeasureData` no longer lives in `Prop` (avoids proof-irrelevance collapse).

- **Explicit compatibility binder introduced for L² vs top‑form integration**
  - File: `Hodge/Analytic/Integration/VolumeForm.lean`
  - `KahlerMeasureCompatibilityData` records agreement between `kahlerMeasure` and
    the top-dimensional Hausdorff measure coming from `SubmanifoldIntegrationData`.
  - Remaining: strengthen this with a top-form integration compatibility lemma.

- **Top‑form compatibility interface added**
  - File: `Hodge/Analytic/Integration/Compatibility.lean`
  - `TopFormIntegralCompatibilityData` records the explicit equality needed to bridge
    `topFormIntegral_real'` with the `kahlerMeasure` integral of the top‑form evaluation.

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

- **Current regularization stub removed**
  - Files: `Hodge/GMT/CurrentToForm.lean`, `Hodge/GMT/PoincareDuality.lean`
  - `regularizeCurrentToForm` is now an explicit data interface
    (`CurrentRegularizationData`), not a zero-form stub.
  - `ClosedSubmanifoldStokesData` is now a data wrapper around `ClosedSubmanifoldData`
    (in `Hodge/Analytic/Currents.lean`), and the proof‑track uses `integrationCurrent_data`
    (explicit `ClosedSubmanifoldData`) rather than wrapper‑based `integrationCurrent`.

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

- **Deep microstructure pillar stubs removed (now explicit data interfaces)**
  - File: `Hodge/Deep/Pillars/Microstructure.lean`
    - `LocalSheetExistsData`, `GluingBoundaryBoundData`, `CalibrationDefectMeshBoundData`.
    - `AutomaticSYRData.real'` now takes an explicit construction argument (no universal stub).

---

## D. Harvey–Lawson / King

- **`IsAnalyticSet` (closed + local holomorphic zero locus) is now real**
  - Status: ✅ FIXED
  - Location: `Hodge/AnalyticSets.lean` (`IsAnalyticSetZeroLocus`)
  - Integrated into the spine at: `Hodge/Classical/HarveyLawson.lean` (`IsAnalyticSet := IsAnalyticSetZeroLocus`)
  - Remaining deep blocker: **Harvey–Lawson regularity**
    (`CalibratedCurrentRegularityData.support_is_analytic_zero_locus`) is still an explicit typeclass binder.

- **Deep Harvey–Lawson pillar stubs removed**
  - File: `Hodge/Deep/Pillars/HarveyLawson.lean`
    - Theorems now rely on `CalibratedCurrentRegularityData`, `HarveyLawsonKingData`,
      and `ChowGAGAData` instead of closedness/`True` placeholders.

- **Harvey–Lawson real bridge placeholder tightened**
  - File: `Hodge/Classical/HarveyLawsonReal.lean`
    - `harvey_lawson_king_decomposition` now returns the explicit `current_eq` witness.
  - Integration currents of analytic varieties are now explicit data
    (`VarietyIntegrationCurrentData`) instead of zero-current stubs.

---

## E. Chow / GAGA

- **`IsAlgebraicSet` (homogeneous polynomial zero loci pulled back from ℙ^N) is now real**
  - Status: ✅ FIXED
  - Location: `Hodge/Classical/AlgebraicSets.lean`
  - Used by: `Hodge/Classical/GAGA.lean` (algebraic subvarieties, closure lemmas, hyperplane/CI examples)
  - Remaining deep blocker: **Chow/GAGA theorem** itself (`ChowGAGAData`) is still an explicit typeclass binder.

- **Deep GAGA pillar stubs removed**
  - File: `Hodge/Deep/Pillars/GAGA.lean`
    - Removed `IsAlgebraicSetStrong` placeholder and `True` stubs; now uses `ChowGAGAData`.

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
