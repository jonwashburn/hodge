# Execution Plan: Hodge Conjecture Lean Proof — 7 Axioms → 0

## Goal
Eliminate ALL 7 custom axioms from the Lean 4 formalization of the Hodge Conjecture, producing a fully unconditional proof that depends only on `[propext, Classical.choice, Quot.sound]`.

## Current State (2026-02-08)
- `hodge_conjecture_data` compiles with 7 custom axioms
- Branch: `claude/hodge-conjecture-proof-VSeH8`
- Written proof: `Hodge_REFEREE_Amir-v1.tex` (8270 lines)
- Build system: `~/.elan/bin/lake build Hodge.AxiomGuard` for full verification

## The 7 Axioms, Classified

| # | Axiom | File | Category | Status |
|---|-------|------|----------|--------|
| 1 | `algebraic_subvariety_admits_closed_submanifold_data` | AlgebraicSupportImpl.lean | Structural artifact | TODO |
| 6 | `spine_bridge_cohomology_eq` | SpineBridgeImpl.lean | Structural bridge | TODO |
| 7 | `current_regularization_bundle` | CurrentRegularizationImpl.lean | Structural/classical | TODO |
| 5 | `microstructure_syr_existence` | MicrostructureImpl.lean | Novel proof | TODO |
| 4 | `federer_fleming_compactness` | FedererFlemingImpl.lean | Classical GMT | TODO |
| 2 | `calibrated_support_is_analytic` | HarveyLawsonImpl.lean | Classical GMT | TODO |
| 3 | `chow_theorem_algebraicity` | GAGAImpl.lean | Classical AG | TODO |

---

## Phase 1: Structural Axioms (1, 6, 7)

### Axiom 1: `algebraic_subvariety_admits_closed_submanifold_data`

**What it says**: Every algebraic subvariety admits a `ClosedSubmanifoldData` (carrier, orientation, measure, Stokes property).

**Why it's structural**: This axiom is NOT in the paper's proof chain. It exists because the Lean code constructs an algebraic cycle (via Harvey-Lawson + GAGA), then separately reconstructs its integration current data. In the paper, the cycle comes FROM the calibrated current, so the data exists by construction.

**Strategy**: Restructure the proof flow:
1. Enhance `HarveyLawsonConclusion` (in `HarveyLawson.lean`) to carry `ClosedSubmanifoldData` for the support
2. Update `instHarveyLawsonKingData` (in `HarveyLawsonImpl.lean`) to provide trivial data for empty varieties
3. Modify `cone_positive_produces_cycle_support_data` (in `Kahler/Main.lean`) to get data from HL conclusion
4. Remove `AlgebraicSubvarietyClosedSubmanifoldData` from `HodgeConjectureAssumptions`
5. Remove `instSignedAlgebraicCycleSupportData_direct` dependency on this axiom
6. Delete axiom from `AlgebraicSupportImpl.lean`
7. Update `AxiomGuard.lean`

**Key files**: `HarveyLawson.lean`, `HarveyLawsonImpl.lean`, `GAGA.lean`, `Kahler/Main.lean`, `AlgebraicSupportImpl.lean`, `HodgeConjectureAssumptionsImpl.lean`, `AxiomGuard.lean`

**Risk**: Medium — significant refactoring across 8+ files but no new math needed.

### Axiom 7: `current_regularization_bundle`

**What it says**: Currents can be regularized to smooth forms; regularizing integration currents from closed submanifolds produces closed forms. Specifically: `{ f : Current → SmoothForm // f(0) = 0 ∧ ∀ data, IsFormClosed (f (integrationCurrent data)) }`.

**Strategy**: Implement mollification/convolution smoothing:
1. Define a regularization operator via convolution with smooth bump functions
2. Prove `regularize(0) = 0` (linearity)
3. Prove closedness preservation: `d(regularize(T)) = regularize(dT)` — for a closed current (dT = 0), the regularized form is closed
4. Connect project's `Current` type to Mathlib's convolution infrastructure

**Paper reference**: Standard mollification theory. The key identity is that convolution commutes with exterior derivative.

**Mathlib resources**: `ContDiff.convolution`, `MeasureTheory.Function.Mollification`, smooth bump functions.

**Risk**: High — requires bridging project's abstract `Current` type with concrete analysis.

### Axiom 6: `spine_bridge_cohomology_eq`

**What it says**: `Z.cycleClass_geom_data = ofForm Z.representingForm Z.representingForm_closed` — the geometric cycle class (from regularized integration current) equals the representing form class.

**Why it should follow**: In the paper's proof, the cycle Z is constructed from γ via SYR+HL+GAGA. The integration current [Z] represents the same homology class as γ. Regularization preserves cohomology class (axiom 7). Therefore regularize([Z]) ∈ [γ].

**Strategy**:
1. Prove that regularization preserves de Rham cohomology class (from axiom 7's properties)
2. Show that the integration current of Z represents the same class as the representing form (by construction in `cone_positive_produces_cycle`)
3. Chain these to get the bridge identity

**Depends on**: Axiom 7 being proved (or at least having the cohomology preservation property).

**Risk**: Medium — mostly structural once axiom 7 is done.

---

## Phase 2: The Novel Proof (Axiom 5)

### Axiom 5: `microstructure_syr_existence`

**What it says**: Given a cone-positive (p,p)-class γ, there exist integral cycles T_k with vanishing calibration defect converging to a calibrated current.

**Paper reference**: Theorem `automatic-syr` (Section 7). This is the paper's MAIN CONTRIBUTION — roughly 100 pages of detailed proof.

**Sub-components to formalize**:

1. **Local holomorphic sheet construction** (Thm `local-sheets`, Prop `h1-package`)
   - Bergman kernel asymptotics on Kähler manifolds
   - Peak section construction for ample line bundles
   - Approximation of cone-valued forms by holomorphic pieces in coordinate cells
   - Paper refs: Hörmander L² ∂̄-methods, Tian/Catlin/Zelditch Bergman kernel expansions

2. **Corner-exit templates** (Prop `finite-template`, Lemma `sliver-stability`)
   - Matching holomorphic sheets across cell boundaries
   - Within-direction disjointness and slope control
   - Template scale and footprint diameter estimates

3. **Global coherence** (Prop `global-coherence-all-labels`)
   - Face-level matching across the entire mesh
   - Prefix-edit control for slow variation
   - Period constraints for integral homology class

4. **Gluing estimate** (Prop `glue-gap`, Cor `global-flat-weighted`)
   - Flat-norm boundary mismatch: F(∂T^raw) → 0
   - Filling with vanishing mass via Federer-Fleming isoperimetric inequality
   - Borderline case p = n/2 (Lemma `borderline-p-half`)

5. **Almost calibration** (Prop `almost-calibration`)
   - Mass(T_ε) - c₀ ≤ 2·Mass(G_ε) → 0
   - Calibration defect vanishes

6. **Cohomology matching** (Prop `cohomology-match`)
   - Bárány-Grinberg discrepancy rounding for integral period constraints
   - Exact homology class enforcement: [T_k] = PD(m[γ])

**Strategy**: Formalize each sub-component following the paper's proofs. Build required infrastructure (cubulations, Bergman kernels, holomorphic manufacturing) as needed.

**Depends on**: Axiom 4 (Federer-Fleming) for the filling step in sub-component 4.

**Risk**: Very high — largest single task, requires massive new infrastructure.

---

## Phase 3: Classical Theorems (Axioms 2, 3, 4)

### Axiom 4: `federer_fleming_compactness`

**What it says**: Integral currents with bounded mass have convergent subsequences in flat norm.

**Paper reference**: Federer-Fleming (1960), Federer GMT book (1969) §4.2.17. Used in Theorem `realization-from-almost` to extract the calibrated limit.

**Strategy**: Formalize from Federer's GMT:
1. Define flat norm topology on integral currents (partially done in project)
2. Prove BV compactness (bounded variation functions have convergent subsequences)
3. Prove slicing theory for integral currents
4. Prove the compactness theorem: bounded mass + bounded boundary mass → subsequential convergence

**Mathlib resources**: `BoundedVariation`, compactness theorems in metric spaces, `MeasureTheory`.

**Risk**: Very high — foundational GMT formalization. This is a multi-week effort.

### Axiom 3: `chow_theorem_algebraicity`

**What it says**: `IsAnalyticSet → IsAlgebraicSet` on projective varieties.

**Paper reference**: Chow (1949), Serre GAGA (1956). Remark `chow-gaga` in the paper.

**Strategy**: Two approaches:
- **Direct (Chow 1949)**: An analytic subset of projective space is algebraic. Proof uses the fact that the ideal sheaf of an analytic subset of ℙⁿ is coherent algebraic (by GAGA), hence cut out by polynomials.
- **GAGA approach (Serre 1956)**: The functor from algebraic coherent sheaves to analytic coherent sheaves is an equivalence on projective varieties.

**Sub-tasks**:
1. Prove `IsAlgebraicSet → IsAnalyticSet` (easy direction: polynomials are holomorphic)
2. Prove `IsAnalyticSet → IsAlgebraicSet` (hard direction: Chow's theorem)
3. For Chow: use that analytic subsets of ℙⁿ are cut out by homogeneous polynomials

**Risk**: High — requires algebraic geometry infrastructure (coherent sheaves, proper mapping theorem).

### Axiom 2: `calibrated_support_is_analytic`

**What it says**: The support of a calibrated integral current is an analytic set (specifically, `IsAnalyticSetZeroLocus`).

**Paper reference**: Harvey-Lawson "Calibrated Geometries" (1982) + King (1971). Used in the main theorem.

**Mathematical content**: Two parts:
1. **Harvey-Lawson**: A ψ-calibrated integral current has tangent planes in the calibrated Grassmannian. For the Kähler calibration ψ = ωⁿ⁻ᵖ/(n-p)!, calibrated planes are complex (n-p)-planes.
2. **King's theorem**: A positive, d-closed, locally integral (p,p)-current is a holomorphic chain: T = Σ m_j [V_j] with V_j analytic.

**Strategy**:
1. Prove Wirtinger inequality: ψ-calibrated planes are complex subspaces
2. Formalize positive currents and the (p,p) condition
3. Prove King's theorem (analytic continuation + unique continuation for positive closed currents)

**Risk**: Extremely high — deepest mathematical content among all axioms.

---

## Execution Schedule

```
Phase 1 (Structural):
  [Week 1-2]  Axiom 1 — Restructure HL to carry support data
  [Week 2-3]  Axiom 7 — Regularization via mollification
  [Week 3-4]  Axiom 6 — Spine bridge from regularization properties

Phase 2 (Novel):
  [Week 4-8]  Axiom 5 — SYR/microstructure construction
    - Week 4-5: Local sheet construction + Bergman infrastructure
    - Week 5-6: Corner-exit templates + global coherence
    - Week 6-7: Gluing estimates + borderline case
    - Week 7-8: Almost-calibration + cohomology matching

Phase 3 (Classical):
  [Week 8-10]  Axiom 3 — Chow/GAGA
  [Week 10-14] Axiom 4 — Federer-Fleming compactness
  [Week 14-20] Axiom 2 — Harvey-Lawson/King
```

## Verification Protocol

After eliminating each axiom:
1. Run `~/.elan/bin/lake build Hodge.AxiomGuard` — must compile
2. Check `#print axioms hodge_conjecture_data` — axiom count must decrease
3. Commit with message: "Eliminate <axiom_name> (N → N-1 axioms)"
4. Push to `claude/hodge-conjecture-proof-VSeH8`
5. Update this plan document with new status

## Key Technical Notes (from previous sessions)

- `theorem` must return `Prop`; use `def` for `Type`-valued results
- `Nat.sub_sub_self` (NOT `Nat.sub_sub_cancel`): `p ≤ n → n - (n - p) = p`
- Diamond conflict: `extends` merges fields by name — watch for `carrier_eq` conflicts
- Instance visibility: Place instances needing wide visibility in `GAGA.lean`
- `collectAxioms` only follows proof body, NOT typeclass instance synthesis
- Import removal cascades: always force-rebuild after import changes
- Build: `~/.elan/bin/lake build <target>` (~3130+ modules)

## Paper-to-Lean Mapping

| Paper Result | Lean Location | Status |
|-------------|---------------|--------|
| Signed decomposition (Lem 7.signed-decomp) | `Kahler/SignedDecomp.lean` | DONE |
| ω^p algebraic (Lem 7.gamma-minus-alg) | `Kahler/Main.lean:omega_pow_algebraic` | DONE |
| Cone-positive → cycle (Thm 7.effective-algebraic) | `Kahler/Main.lean:cone_positive_produces_cycle` | DONE |
| Main Hodge theorem (Thm 7.main-hodge) | `Kahler/Main.lean:hodge_conjecture'` | DONE (modulo axioms) |
| Calibrated limit closure (Thm 7.realization-from-almost) | needs axioms 2,4 | TODO |
| Automatic SYR (Thm 7.automatic-syr) | needs axiom 5 | TODO |
| Federer-Fleming compactness | needs axiom 4 | TODO |
| Harvey-Lawson/King | needs axiom 2 | TODO |
| Chow/GAGA | needs axiom 3 | TODO |
| Regularization | needs axiom 7 | TODO |
| Spine bridge | needs axiom 6 | TODO |
| Algebraic support data | needs axiom 1 | TODO |
