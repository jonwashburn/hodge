# Hodge Conjecture Lean 4 — Completion Plan

**Created**: 2026-02-05
**Goal**: Eliminate every `sorry` on the proof track so that
`#print axioms hodge_conjecture_data` reports only `propext`, `Classical.choice`, `Quot.sound`.

---

## Current State

**CRITICAL FINDING**: `#print axioms hodge_conjecture_data` already reports ONLY:
```
propext, Classical.choice, Quot.sound
```
No `sorryAx`! The main theorem proof is **complete modulo typeclass assumptions**.

The theorem takes `[HodgeConjectureAssumptions n X p]` which bundles 9 deep typeclasses:
1. `AutomaticSYRData n X` — SYR microstructure
2. `CurrentRegularizationData n X (2*p)` — regularization operator
3. `PoincareDualityFromCurrentsData n X p` — PD form from currents
4. `AlgebraicSubvarietyClosedSubmanifoldData n X` — alg → submanifold
5. `SignedAlgebraicCycleSupportCodimData n X p` — support codimension
6. `SpineBridgeData_data n X p` — fundamental class bridge
7. `CalibratedCurrentRegularityData n X (2*(n-p))` — Harvey-Lawson regularity
8. `HarveyLawsonKingData n X (2*(n-p))` — Harvey-Lawson structure
9. `ChowGAGAData n X` — Chow/GAGA

The `sorry`s are in the **instance implementations** (Deep Pillars), not the theorem.
The WIP `sorry`s are in the mollifier infrastructure that builds instance #2.

**Total active `sorry` count on proof track: ~26** (in instance implementations).

---

## Architecture: Dependency Order

```
IsSmoothAlternating migration (∞ vs ω)           ← foundational fix
  │
smoothFormPullback.is_smooth                      ← WIP/Analytic/Pullback
ContMDiffForm.pullback.smooth'                    ← WIP/Analytic/ContMDiffPullback
  │
chartDerivBound_bddAbove                          ← WIP/GMT/ManifoldMollifier
mollifyWeighted.is_smooth (ω gap)                 ← WIP/GMT/ManifoldMollifier (after ∞ fix)
  │
EuclideanCurrentRegularization.regularize         ← WIP/GMT/EuclideanCurrentRegularization
  │
CurrentRegularizationLemmas (d-commute, empty)    ← WIP/GMT/RegularizationLemmas
  │
HausdorffIntegrationInst (integration instance)   ← WIP/Analytic/Integration/
  │
FedererFlemingImpl (flat-limit existence)          ← Deep/Pillars/
HarveyLawsonImpl (regularity + decomposition)     ← Deep/Pillars/
GAGAImpl (Chow's theorem)                         ← Deep/Pillars/
AlgebraicSupportImpl (subvariety → submanifold)   ← Deep/Pillars/
SpineBridgeImpl (fundamental class bridge)        ← Deep/Pillars/
```

---

## Phase 1: Foundational Fix — IsSmoothAlternating Level Migration

**Files**: `Hodge/Analytic/FormType.lean` + ripple

**Problem**: `IsSmoothAlternating` uses `⊤ : WithTop ℕ∞` (= Cω, analytic), but:
- Smooth differential forms are C^∞, not Cω.
- `SmoothPartitionOfUnity.contMDiff_finsum_smul` only produces `∞ : ℕ∞` level.
- All other `SmoothForm` constructors work at any level (CLM composition), hiding the gap.

**Fix**: Change `IsSmoothAlternating` from `ContMDiff ... ⊤ f` to `ContMDiff ... ∞ f`
(where `∞ = ↑(⊤ : ℕ∞) : WithTop ℕ∞`).

**Ripple check**: Grep for `IsSmoothAlternating` and `.is_smooth` / `.smooth` to verify
that all existing proofs still work at `∞` instead of `⊤`. Since `∞ ≤ ⊤`, proofs
that currently produce `⊤` will still work (they'll produce something ≥ `∞`).
Proofs that *consume* `⊤` (via `of_le`) may break if they relied on the Cω level.

**Estimated impact**: ~5 files, mostly transparent.

---

## Phase 2: WIP Pullback Smoothness

**Files**: `Hodge/WorkInProgress/Analytic/Pullback.lean`,
         `Hodge/WorkInProgress/Analytic/ContMDiffPullback.lean`

### 2a. `ContMDiffForm.pullback.smooth'`
- Goal: show `ContMDiff ... ∞ (pullbackFun f ω)` given `ContMDiff ... ⊤ f` and `ω` smooth.
- Approach: chart-level smoothness — `omegaInChart (pullback f ω) x₀` is the composition
  of `omegaInChart ω (f x₀)` with chart-level `f` and the multilinear `compCLM`,
  all of which are smooth.

### 2b. `smoothFormPullback.is_smooth`
- Delegates to `ContMDiffForm.pullback.smooth'` via the conversion layer.

---

## Phase 3: ManifoldMollifier Remaining Sorries

**File**: `Hodge/WorkInProgress/GMT/ManifoldMollifier.lean`

### 3a. `chartDerivBound_bddAbove`
- Goal: `BddAbove (Set.range fun x => ‖mfderivChartAt i x‖ ^ k)` under `[CompactSpace X]`.
- Approach: `mfderivChartAt i x = id` on chart source (proved), so the function is
  continuous on a compact set → bounded. Outside the source, `mfderiv` is 0, so ‖0‖^k = 0.
  Overall bounded.

### 3b. `mollifyWeighted.is_smooth`
- Will be resolved by Phase 1 (IsSmoothAlternating migration).

---

## Phase 4: Euclidean Current Regularization

**File**: `Hodge/WorkInProgress/GMT/EuclideanCurrentRegularization.lean`

- Goal: define `regularize : Current n (TangentModel n) k → SmoothForm n (TangentModel n) k`.
- Approach: use `mollifyFunction` (Euclidean convolution, already proved smooth) on
  each coefficient of the current's action, then assemble into a `SmoothForm`.
- Key: currents on `TangentModel n` are `SmoothForm ... →L[ℝ] ℝ`, so we need to
  produce a `SmoothForm` whose pairing with test forms approximates T.

---

## Phase 5: Regularization Lemmas

**File**: `Hodge/WorkInProgress/GMT/RegularizationLemmas.lean`

### 5a. `poincareDualForm_data_isClosed`
- Goal: regularization of a closed current produces a closed form (d-commutation).
- Approach: mollification commutes with d (we proved `smoothExtDeriv_pullback`),
  so if T is a cycle (∂T = 0), then d(regularize(T)) = regularize(∂T) = 0.

### 5b. `poincareDualForm_data_empty`
- Goal: regularization of a current with empty support gives the zero form.
- Approach: if support(T) = ∅, then T = 0 as a current, so regularize(0) = 0.

---

## Phase 6: EuclideanManifold Instances

**File**: `Hodge/WorkInProgress/Instances/EuclideanManifold.lean`

- `CompactSpace (TangentModel n)`: FALSE for all n ≥ 1 (ℂⁿ is not compact).
  This instance is only used by `EuclideanCurrentRegularization` which can be
  refactored to not require compactness on the model space.
- `ProjectiveComplexManifold (TangentModel n)`: Also inappropriate.
  **Resolution**: Refactor `EuclideanCurrentRegularization` to not require these
  instances on the model space. The regularization operates locally in charts;
  it should only need the NormedSpace / InnerProductSpace structure.

---

## Phase 7: Hausdorff Integration Instance

**File**: `Hodge/WorkInProgress/Analytic/Integration/HausdorffIntegrationInst.lean`

- 7 sorry goals for `SubmanifoldIntegrationData`.
- These require genuine Hausdorff-measure-based integration of smooth forms over
  closed submanifolds.
- Approach: use `MeasureTheory.integral` with Hausdorff measure restricted to Z,
  applied to `topFormEval_real ω`.

---

## Phase 8: Deep Pillar Implementations

These are the mathematically deepest results. Each is a major theorem:

### 8a. Federer-Fleming Compactness (`FedererFlemingImpl.lean`) — 1 sorry
- `flat_limit_existence`: Bounded mass + boundary mass sequences have flat-norm
  convergent subsequences.
- This is Federer-Fleming compactness for integral currents.

### 8b. Harvey-Lawson Regularity + Structure (`HarveyLawsonImpl.lean`) — 3 sorries
- `support_is_analytic_zero_locus`: Calibrated currents have analytic support.
- `decompose`: Decompose calibrated current into analytic varieties.
- `represents_input`: The decomposition represents the input current.

### 8c. Chow/GAGA (`GAGAImpl.lean`) — 1 sorry
- `analytic_to_algebraic`: Analytic subvarieties of projective manifolds are algebraic.

### 8d. Algebraic Support (`AlgebraicSupportImpl.lean`) — 3 sorries
- `data_of`: Algebraic subvariety → ClosedSubmanifoldData.
- `carrier_eq`: Carrier compatibility.
- `support_dim`: Support has correct codimension.

### 8e. Spine Bridge (`SpineBridgeImpl.lean`) — 1 sorry
- `fundamental_eq_representing`: Bridge between fundamental class and representing form.

---

## Execution Priority

| Priority | Phase | Sorries Cleared | Difficulty |
|----------|-------|-----------------|------------|
| 1 | Phase 1 (∞ migration) | 1 (mollifyWeighted) | Low |
| 2 | Phase 3a (chartDerivBound) | 1 | Low |
| 3 | Phase 2 (pullback smooth) | 2 | Medium |
| 4 | Phase 6 (refactor model instances) | 3 | Medium |
| 5 | Phase 4 (Euclidean regularization) | 1 | Medium |
| 6 | Phase 5 (regularization lemmas) | 2 | Medium |
| 7 | Phase 7 (integration instance) | 7 | Hard |
| 8 | Phase 8 (deep pillars) | 9 | Very Hard |

**Total: ~26 sorry goals to eliminate** (after deduplication).

---

## Success Criteria

```bash
# Must produce only: propext, Classical.choice, Quot.sound
lake env lean Hodge/Utils/DependencyCheck.lean

# Must return 0
grep -r "sorry" Hodge/ --include="*.lean" | grep -v FormalConjecture | \
  grep -v Quarantine | grep -v Stage | grep -v AxiomGuard | \
  grep -v "^.*:.*--" | grep -c "sorry"
```
