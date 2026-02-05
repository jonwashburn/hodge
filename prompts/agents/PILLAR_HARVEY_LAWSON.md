# Agent Task: HarveyLawsonImpl — Harvey-Lawson Structure Theorem

## Target File
`Hodge/Deep/Pillars/HarveyLawsonImpl.lean`

## Sorries to Eliminate (3)

### 1. `support_is_analytic_zero_locus` (line ~27)
**Type**: For calibrated integral currents, support is a local holomorphic zero locus
**Goal**: Harvey-Lawson regularity — calibrated currents have analytic support

**Mathematical Content** (Harvey-Lawson, Acta Math 1982):
A ψ-calibrated integral current on a Kähler manifold has support that is a complex
analytic subvariety. The support is locally the zero locus of holomorphic functions.

### 2. `decompose` (line ~38)
**Type**: `(hyp : HarveyLawsonHypothesis n X k) → HarveyLawsonConclusion n X k`
**Goal**: Decompose a calibrated current into a finite sum of irreducible analytic varieties
with integer multiplicities.

**Mathematical Content** (Harvey-Lawson + King 1971):
A positive d-closed integral current of bidimension (p,p) is a holomorphic chain:
  T = Σ m_j [V_j]
where m_j ∈ ℕ and V_j are irreducible complex analytic subvarieties.

### 3. `represents_input` (line ~41)
**Type**: Proof that the decomposition represents the input current
**Goal**: The constructed HarveyLawsonConclusion faithfully represents the input

**Strategy for all three**:
1. Read `HarveyLawsonHypothesis` and `HarveyLawsonConclusion` structures
2. Read existing infrastructure in `Hodge/Deep/Pillars/HarveyLawson.lean` (134 lines)
3. Read `Hodge/Classical/HarveyLawson.lean` for the interface
4. The non-Impl file may have partial proofs or lemmas to build on
5. Check if the proof can be built from the existing calibration infrastructure
   in `Hodge/Analytic/Calibration.lean`

**Approach**:
- For #1: May be provable from calibration properties + analytic set definitions
- For #2: Build the conclusion structure with the decomposition data
- For #3: Show the decomposition matches the input by construction

## Key Files to Read
- `Hodge/Deep/Pillars/HarveyLawsonImpl.lean` (target)
- `Hodge/Deep/Pillars/HarveyLawson.lean` (infrastructure)
- `Hodge/Classical/HarveyLawson.lean` (typeclass interface)
- `Hodge/Analytic/Calibration.lean` (calibration theory)

## Verification
```bash
lake build Hodge.Deep.Pillars.HarveyLawsonImpl
```
