# Semantic Gotchas Index (Proof-Track Blockers)

This file is a **living index** of remaining “no gotchas” blockers: definitions and instances that still trivialize the intended mathematics even though the repo currently compiles and the audits are green.

The intent is to make it easy for the integrator (and bounded agents) to find and eliminate semantic cheats without “passing the audit by changing the audit”.

---

## WIP Sorries Register (off proof track)

These sorries live only in WIP files (`Hodge/WorkInProgress/**` or `Hodge/Deep/Pillars/*Impl.lean`)
and must remain unimported by the proof track (`Hodge/Main.lean`, `Hodge.lean`).

- `Hodge/WorkInProgress/GMT/RegularizationLemmas.lean:17-23` — `CurrentRegularizationLemmas` instance (closedness on cycles + empty-carrier vanishing).
- `Hodge/WorkInProgress/Analytic/Pullback.lean:36-42` — `smoothFormPullback` smoothness proof (chart-level pullback infrastructure).
- `Hodge/WorkInProgress/Analytic/ContMDiffPullback.lean:20-26` — `ContMDiffForm.pullback` smoothness proof.
- `Hodge/WorkInProgress/Analytic/ContMDiffPullback.lean:33-40` — `extDerivForm_pullback` (pullback commutes with exterior derivative).
- `Hodge/WorkInProgress/GMT/ManifoldMollifier.lean:45-52` — `chartDerivBound_bddAbove` (global bound still missing; local continuity added).
- `Hodge/WorkInProgress/GMT/EuclideanCurrentRegularization.lean:12-18` — `EuclideanCurrentRegularizationData` (regularization interface on model space).
- `Hodge/WorkInProgress/GMT/EuclideanCurrentRegularization.lean:24-30` — `instEuclideanCurrentRegularizationData` (definition by chartwise convolution).
- `Hodge/WorkInProgress/Instances/EuclideanManifold.lean:28-30` — `instCompactSpace_TangentModel` (compactness placeholder).
- `Hodge/WorkInProgress/Instances/EuclideanManifold.lean:32-46` — `instProjectiveComplexManifold_TangentModel` (projective manifold structure).
- `Hodge/WorkInProgress/Instances/EuclideanManifold.lean:48-51` — `instKahlerManifold_TangentModel` (Kähler structure on model space).
- `Hodge/WorkInProgress/Analytic/Integration/HausdorffIntegrationInst.lean:30-42` — `SubmanifoldIntegrationData` instance: finite Hausdorff measure, oriented integral, linearity/union/empty/bound, and Stokes.
- `Hodge/Deep/Pillars/FedererFlemingImpl.lean:23-29` — `FlatLimitExistenceData.flat_limit_existence` (Federer–Fleming compactness in flat norm).
- `Hodge/Deep/Pillars/HarveyLawsonImpl.lean:23-27` — `CalibratedCurrentRegularityData.support_is_analytic_zero_locus` (Harvey–Lawson regularity).
- `Hodge/Deep/Pillars/HarveyLawsonImpl.lean:35-41` — `HarveyLawsonKingData.decompose` + `represents_input` (Harvey–Lawson/King decomposition and representation).
- `Hodge/Deep/Pillars/GAGAImpl.lean:23-27` — `ChowGAGAData.analytic_to_algebraic` (Chow/GAGA).
- `Hodge/Deep/Pillars/SpineBridgeImpl.lean:35-41` — `SpineBridgeData_data.fundamental_eq_representing` (spine bridge theorem).
- `Hodge/Deep/Pillars/AlgebraicSupportImpl.lean:25-31` — `AlgebraicSubvarietyClosedSubmanifoldData.data_of` + `carrier_eq` (closed submanifold data for algebraic subvarieties).
- `Hodge/Deep/Pillars/AlgebraicSupportImpl.lean:39-44` — `SignedAlgebraicCycleSupportCodimData.support_dim` (codimension of signed cycle support).

## A. Cycle class / fundamental class

- **`SignedAlgebraicCycle.cycleClass_geom_data` is NOW CORRECT (Phase 7, 2026-02-01)**
  - Status: ✅ FIXED
  - Location: `Hodge/Classical/GAGA.lean:522-555`
  - Change: `cycleClass_geom_data` is defined using `FundamentalClassSet_data(support_data)`, NOT as `Z.cycleClass`.
  - The proof spine uses `SpineBridgeData_data` (data‑first), not `rfl`.
  - **REMAINING**: The theorem `hodge_conjecture'` (data‑first) requires typeclass parameters:
    - `[CycleClass.PoincareDualityFromCurrentsData n X p]` - PD form from integration current
    - `[SpineBridgeData_data n X]` - Bridge between geometric class and representing form
  - These encode **real mathematical content** that requires de Rham representability + Harvey-Lawson.
  - **Compatibility wrappers cleared (2026-02-05)**: set‑based `hodge_conjecture` / `cycleClass_geom`
    wrappers were removed from the proof‑track files; the main theorem is now the
    data‑first `hodge_conjecture'`.

- **`FundamentalClassSet_data` requires `PoincareDualityFromCurrentsData`**
  - Location: `Hodge/Classical/GAGA.lean:337-370` (`FundamentalClassSet_data`)
  - Location: `Hodge/Classical/PoincareDualityFromCurrents.lean` (`fundamentalClassImpl_data_fromCurrents`)
  - The proof track requires `PoincareDualityFromCurrentsData`, which yields
    `PoincareDualFormFromCurrentData` as a derived instance for legacy helpers.
  - Status: The interface is correct; no `.universal` stub exists.
  - `PoincareDualFormData` no longer carries stub fields (`nonzero_possible`, `geometric_characterization`).
  - **Data-first update**: `poincareDualForm_data` is **definitionally** the regularization of
    `integrationCurrent_data`. The legacy `PoincareDualFormExists_data` interface remains
    compatibility‑only; the proof spine uses `PoincareDualityFromCurrentsData`.
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

- **Current regularization still missing (no concrete instance)**
  - Status: ❌ BLOCKED (2026-02-04)
  - Locations:
    - `Hodge/GMT/CurrentToForm.lean:24-40` (`CurrentRegularizationData` + `regularizeCurrentToForm`)
    - `Hodge/GMT/HeatKernelRegularization.lean:34-62` (scaffolding only; no operator)
    - `Hodge/WorkInProgress/GMT/ManifoldMollifier.lean:18-24` (WIP manifold patching scaffold)
    - `Hodge/WorkInProgress/GMT/RegularizationLemmas.lean:17-23` (WIP regularization lemma instances)
    - `Hodge/GMT/RegularizationLemmas.lean:53-66` (`CurrentRegularizationLemmas` checklist)
    - `Hodge/Classical/PoincareDualityFromCurrents.lean:40-53` (PD interface requirements)
    - `Hodge/Analytic/Stage2/IntegrationCurrentsManifoldSkeleton.lean:174-214` (pullback infrastructure TODOs)
  - Missing lemmas:
    - `CurrentRegularizationLemmas.poincareDualForm_data_isClosed`
    - `CurrentRegularizationLemmas.poincareDualForm_data_empty`
  - Blocker: requires a genuine current‑regularization operator (heat kernel/mollifier on charts
    with partition of unity) plus **chart‑level pullback/pushforward for forms/currents** and
    proofs of closedness on cycles and empty‑carrier vanishing.
- **Legacy set-based PD placeholder (`omegaPower`)**
  - Location: `Hodge/Classical/CycleClass.lean:140-210` (`omegaPower`)
  - Status: Compatibility‑only (no universal instance is provided; not used on the data‑first spine).
  - **REMAINING**: Replace with a real integration‑current construction + de Rham representability.

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

- **Chow/GAGA instance provided (with sorries)**
  - Status: 🚧 SCAFFOLDED (2026-02-04)
  - Locations:
    - `Hodge/Deep/Pillars/GAGAImpl.lean` (instance)
  - Details:
    - `instChowGAGAData` is provided with `sorry` for Chow's theorem.
    - `IsAlgebraicSet` and `IsAnalyticSet` are real definitions.
  - This resolves the "missing instance" blocker for the deep track.

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

- `hodge_conjecture_data` DOES use deep typeclass parameters (NOT hidden):
  - `[AutomaticSYRData n X]`
  - `[CycleClass.PoincareDualityFromCurrentsData n X p]` (→ `PoincareDualFormFromCurrentData`)
  - `[SpineBridgeData_data n X p]`
  - `[CalibratedCurrentRegularityData n X (2*(n-p))]`
  - `[HarveyLawsonKingData n X (2*(n-p))]`
  - `[ChowGAGAData n X]`
  - These encode **real mathematical content** (de Rham representability + Harvey-Lawson bridge)
  - **No `.universal` instances exist for these** - intentionally kept as open requirements

- `FlatLimitCycleData` is now treated as a proved infrastructure lemma (an `instance` exists),
  and it has been removed from the statement of `hodge_conjecture_data` and its downstream theorems.

- The proof of `hodge_conjecture_data` now uses `SpineBridgeData_data.fundamental_eq_representing` (NOT `rfl`):
  - `Hodge/Kahler/Main.lean:642` uses `SignedAlgebraicCycle.cycleClass_geom_data_eq_representingForm`

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
