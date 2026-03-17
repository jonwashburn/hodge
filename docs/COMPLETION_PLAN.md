# Complete Plan to Make `hodge_conjecture_data` Unconditional

**Date**: 2026-03-17
**Author**: Generated from codebase audit
**Status**: Living document — update as axioms are eliminated

---

## Current State

`hodge_conjecture_data` depends on exactly `[propext, Classical.choice, Quot.sound]` at the Lean kernel level (the standard CIC axioms). The `AxiomGuard` allows 10 project-specific axioms that are reachable through the `HodgeConjectureAssumptions` typeclass instance chain. The 2 `sorry` items are in an off-track WIP Hausdorff integration file and do not affect the proof track.

### Dependency chain

```
hodge_conjecture_data (Hodge/Main.lean)
  └── hodge_conjecture' [HodgeConjectureAssumptions n X p]
        └── instHodgeConjectureAssumptions (HodgeConjectureAssumptionsImpl.lean)
              ├── AutomaticSYRData           ← A10
              ├── CurrentRegularizationData   ← A1, A2, A3
              ├── PoincareDualityFromCurrentsData  (derived from above)
              ├── SignedAlgebraicCycleSupportData   ← A7, A8
              ├── SpineBridgeData_data        ← A9
              ├── CalibratedCurrentRegularityData  ← A5
              ├── HarveyLawsonKingData        ← A5
              ├── FlatLimitExistenceData      ← A4
              └── ChowGAGAData               ← A6
```

---

## The 10 Axioms

### Tier 1: Infrastructure axioms (provable with moderate Lean/Mathlib work)

#### A1. `chart_deriv_bound_exists`

Chart derivative norms are bounded on compact manifolds.

| Field | Value |
|-------|-------|
| **Location** | `Hodge/WorkInProgress/GMT/ManifoldMollifier.lean:467` |
| **Type** | `∃ (bound : X → ℝ), ∀ (i x : X), ‖mfderivChartAt i x‖^k ≤ bound i` |
| **Math** | On a compact manifold with locally constant charts, chart derivative norms are uniformly bounded at each chart center. |
| **Why provable** | On `(chartAt i).source`, the derivative equals `id` (proved as `mfderivChartAt_eq_id`). Off-source, `mfderiv` returns 0 (by Mathlib definition when not `MDifferentiableAt`). So the bound is just `‖id‖^k`. |
| **What's needed** | Show that `mfderiv` is 0 outside chart source for `chartAt`, or use `max (‖id‖^k) (sSup ...)` with compactness. |
| **Estimated effort** | 50–100 lines of Lean |

#### A2. `chart_contMDiff`

Chart maps are globally smooth on compact manifolds.

| Field | Value |
|-------|-------|
| **Location** | `Hodge/WorkInProgress/GMT/ManifoldMollifier.lean:488` |
| **Type** | `∀ (x : X), ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ (chartAt H x)` |
| **Math** | On a compact projective Kähler manifold, each chart map extends to a globally smooth map. |
| **Why harder** | `chartAt` as a total function is NOT smooth outside its source. This axiom is used because `currentPushforward` and `smoothFormPullback` take globally smooth maps. The real fix is to refactor these to use source-restricted operations (`ContMDiffOn`), then this axiom becomes unnecessary. |
| **What's needed** | Refactor `currentPushforward`, `smoothFormPullback`, and `mollifyChart` to use `contMDiffOn_chart` (from Mathlib) instead of global `ContMDiff`. This is a structural refactor but mathematically straightforward. |
| **Estimated effort** | 300–500 lines |

#### A3. `euclidean_regularize_isClosed_of_isCycleAt`

Euclidean convolution sends cycles to closed forms.

| Field | Value |
|-------|-------|
| **Location** | `Hodge/WorkInProgress/GMT/EuclideanCurrentRegularization.lean:720` |
| **Type** | `T.isCycleAt → IsFormClosed (regularizeCurrentEuclidean T)` |
| **Math** | On the Euclidean model space, bump-function convolution sends cycle currents (∂T = 0) to closed forms. This is the Euclidean case of `d ∘ mollify = mollify ∘ d`. |
| **Why provable** | (1) Differentiate `T(φ_{x,i})` w.r.t. `x` using continuity of `T`. (2) Use `∂_x bump(x-y) = -∂_y bump(x-y)`. (3) T applied to the y-derivative of the test form equals `(∂T)(test form) = 0` for cycles. |
| **What's needed** | Formalize "differentiation under a continuous linear functional" for the specific translation-BCF family. The key ingredient `hasFDerivAt_translateBCF` is already proved. Then show the `fderiv` of the regularized form factors through the boundary operator. |
| **Estimated effort** | 200–400 lines |

### Tier 2: Deep geometric/analytic theorems (each a substantial Lean project)

#### A4. `federer_fleming_compactness`

Compactness for integral currents.

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Deep/Pillars/FedererFlemingImpl.lean:32` |
| **Math** | Every sequence of integral k-currents with uniformly bounded mass and boundary mass has a subsequence converging in flat norm. This is the BV compactness theorem lifted to currents on manifolds. |
| **What's needed** | Formalize Ambrosio-Kirchheim or Federer-Fleming compactness. Requires: BV function compactness on ℝ^n (partially in Mathlib), slicing theory for currents, deformation theorem. |
| **Estimated effort** | 3,000–10,000 lines. Could be parallelized. |
| **References** | Federer & Fleming, "Normal and integral currents" (1960); Ambrosio & Kirchheim (2000) |

#### A5. `calibrated_support_is_analytic`

Harvey-Lawson regularity.

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Deep/Pillars/HarveyLawsonImpl.lean:30` |
| **Math** | The support of a calibrated integral current on a Kähler manifold is an analytic zero locus. |
| **What's needed** | Formalize Harvey-Lawson theory (1982). Requires: unique continuation for solutions of elliptic PDE, regularity for minimizing currents, the specific structure theorem for calibrated submanifolds. Deeply intertwined with elliptic regularity theory. |
| **Estimated effort** | 5,000–15,000 lines. One of the hardest axioms to eliminate. |
| **References** | Harvey & Lawson, "Calibrated geometries" (1982) |

#### A6. `chow_theorem_algebraicity`

Chow's theorem / GAGA.

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Deep/Pillars/GAGAImpl.lean:30` |
| **Math** | Every closed analytic subset of a projective variety is algebraic. |
| **What's needed** | Formalize GAGA (Serre, 1956) or Chow's theorem. Requires: coherent sheaf theory on projective varieties, comparison between algebraic and analytic cohomology, Cartan's theorem B for Stein manifolds. Alternatively, one can formalize the direct proof of Chow's theorem using degree arguments. |
| **Estimated effort** | 5,000–20,000 lines. Requires significant algebraic geometry infrastructure not in Mathlib. |
| **References** | Serre, "Géométrie algébrique et géométrie analytique" (1956); Chow (1949) |

#### A7. `algebraic_subvariety_admits_closed_submanifold_data`

Algebraic subvarieties carry closed submanifold data.

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Deep/Pillars/AlgebraicSupportImpl.lean:35` |
| **Math** | Every algebraic subvariety V has a `ClosedSubmanifoldData` with carrier = V.carrier — it carries orientation, finite Hausdorff measure, and Stokes compatibility. |
| **What's needed** | Formalize: (1) algebraic subvarieties of projective space are rectifiable sets, (2) they have canonical orientation from the complex structure, (3) Hausdorff measure is finite (by degree theory), (4) Stokes' theorem holds on algebraic subvarieties (via resolution of singularities or direct arguments). |
| **Estimated effort** | 2,000–5,000 lines |

#### A8. `algebraic_codimension_of_cycle_support`

Codimension is carrier-determined.

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Deep/Pillars/AlgebraicSupportImpl.lean:71` |
| **Math** | If W.carrier = Z.support for an algebraic subvariety W and a signed cycle Z of parameter p, then n − W.codim = p. |
| **What's needed** | Show that the dimension of an irreducible algebraic variety is determined by its underlying set. This follows from the definition of dimension for algebraic varieties (transcendence degree = Krull dimension). Requires: basic dimension theory for algebraic varieties. |
| **Estimated effort** | 500–1,500 lines if algebraic variety infrastructure is available |

### Tier 3: The proof spine (requires Tier 1 + Tier 2)

#### A9. `spine_bridge_cohomology_eq`

The geometric cycle class equals the de Rham class.

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Deep/Pillars/SpineBridgeImpl.lean:37` |
| **Math** | `Z.cycleClass_geom_data = ofForm Z.representingForm Z.representingForm_closed` — regularization of the integration current [Z] represents the same de Rham class as Z's representing form. |
| **What's needed** | (1) Regularization preserves cohomology (the regularized form is cohomologous to the current). (2) De Rham theorem (currents and forms represent the same cohomology). Depends on A3 being fully proved and on formalizing the de Rham isomorphism. |
| **Estimated effort** | 2,000–5,000 lines |
| **References** | de Rham, "Variétés Différentiables" (1955) |

#### A10. `microstructure_syr_existence`

Automatic SYR (microstructure) existence.

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Deep/Pillars/MicrostructureImpl.lean:38` |
| **Math** | For any cone-positive form and calibrating form, there exists a sequence of integral cycles converging to a calibrated limit. |
| **What's needed** | Formalize the microstructure/cubulation construction: (1) decompose the manifold into charts, (2) construct local holomorphic sheets in each chart, (3) glue across charts, (4) control boundary defects, (5) apply Federer-Fleming compactness. This is the novel mathematical contribution of the proof strategy. |
| **Estimated effort** | 5,000–15,000 lines. Depends on A4. |

---

## Recommended Execution Order

```
Phase 1: Infrastructure (weeks 1–4)
├── A1: chart_deriv_bound_exists         [prove directly, ~100 lines]
├── A2: chart_contMDiff                  [refactor to ContMDiffOn, ~400 lines]
└── A3: euclidean_regularize_isClosed    [prove via hasFDerivAt_translateBCF, ~300 lines]

Phase 2: Algebraic Foundations (weeks 2–8, parallelizable with Phase 1)
├── A8: algebraic_codimension            [dimension theory, ~1000 lines]
└── A7: algebraic_subvariety_data        [rectifiability + orientation, ~3000 lines]

Phase 3: Hard Analysis (months 2–6, parallelizable)
├── A4: federer_fleming_compactness      [BV compactness + currents, ~5000 lines]
├── A5: calibrated_support_is_analytic   [Harvey-Lawson regularity, ~10000 lines]
└── A6: chow_theorem_algebraicity        [GAGA/Chow theorem, ~10000 lines]

Phase 4: Proof Spine (months 4–8, after Phases 2–3)
├── A9: spine_bridge_cohomology_eq       [de Rham + regularization, ~3000 lines]
└── A10: microstructure_syr_existence    [cubulation + gluing, ~10000 lines]
```

---

## Estimated Total

| Metric | Estimate |
|--------|----------|
| **Additional lines of Lean** | 40,000–60,000 |
| **Calendar time** | 6–12 months with a dedicated team |
| **Team size** | 3–5 formalization experts working in parallel |
| **Critical path** | Phase 3 (hard analysis) is the bottleneck |

---

## Immediate Next Steps

1. **A1** is essentially already proved — just needs the off-source `mfderiv = 0` case. Could be done in a single session.
2. **A2** requires the `ContMDiffOn` refactor of `currentPushforward`/`smoothFormPullback`. Most impactful structural improvement available now.
3. **A3** has all ingredients in place (`hasFDerivAt_translateBCF`, `shifted_bump_contDiff_joint`). The proof is a careful chain of `fderiv` commutation lemmas. Most mathematically satisfying next target.
