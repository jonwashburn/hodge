# Hodge Conjecture Lean Formalization: Sprint Plan

**Generated:** 2024-12-30  
**Goal:** Build a complete, unconditional, machine-checkable proof of the Hodge Conjecture in Lean 4  
**Current axiom count:** 38  
**Target axiom count:** ~30 (remove 8 strategy-critical axioms this sprint)

---

## 🎯 MISSION STATEMENT

We are building a **complete, unconditional, machine-checkable proof** of the Hodge Conjecture in Lean 4. This is not a sketch, not a proof-of-concept, and not an approximation. Every statement must be rigorously proven with no gaps.

**The proof is based on:** `Hodge-v6-w-Jon-Update-MERGED.tex` (the calibration-coercivity approach)

---

## 🚫 ABSOLUTE RULES — NO EXCEPTIONS

### 1. NO SHORTCUTS

| Forbidden | Why |
|-----------|-----|
| `sorry` | Leaves proof incomplete |
| `admit` | Same as sorry |
| `trivial` | Often hides real work |
| `by decide` | Usually wrong for infinite types |
| `native_decide` | Not a proof |

**If you cannot prove something:** Stop and document why. Do NOT use `sorry` as a placeholder.

### 2. MATHLIB FIRST

Before writing ANY proof:
```bash
# Search for existing lemmas
grep -r "KEYWORD" .lake/packages/mathlib/Mathlib/ | head -30

# Check specific modules
grep -r "sSup\|iSup" .lake/packages/mathlib/Mathlib/Topology/Order/ | head -20
```

**Key Mathlib paths:**
- `Mathlib.Analysis.Normed.*` — norms, normed spaces
- `Mathlib.Analysis.InnerProductSpace.*` — inner products
- `Mathlib.Geometry.Manifold.*` — manifolds, tangent spaces
- `Mathlib.LinearAlgebra.*` — exterior algebra, alternating maps
- `Mathlib.Topology.*` — compactness, continuity
- `Mathlib.Analysis.Convex.*` — convex sets, cones
- `Mathlib.Order.ConditionallyCompleteLattice.*` — sSup, iSup
- `Mathlib.CategoryTheory.Abelian.*` — abelian categories, filtrations

### 3. BUILD STRATEGY

```bash
# Prefer file-level builds (faster feedback)
lake build Hodge.Analytic.Norms

# Only use full build when changing imports
lake build

# Check for errors explicitly
lake build Hodge.YourFile 2>&1 | grep -E "error:|warning:"

# Check axiom dependencies
lake env lean DependencyCheck.lean
```

### 4. PROOF METHODOLOGY

1. **Read and understand** the mathematical content
2. **Search Mathlib** for existing results
3. **Write the type signature** first
4. **Build incrementally** — test each lemma compiles
5. **Document** any mathematical subtleties

### 5. COORDINATION

- Each agent owns specific axioms — do NOT edit others' axioms without coordination
- If you need something from another agent's file, create an interface axiom that THEY must prove
- Check build status before starting each session
- Update progress at the end of each session

---

## 📜 AXIOM POLICY

### ✅ ALLOWED AXIOMS (Classical Pillars)

These are **major theorems from the mathematical literature** that are acceptable as axioms:

| Axiom | Reference | Why Allowed |
|-------|-----------|-------------|
| `hard_lefschetz_inverse_form` | Lefschetz 1924, Hodge 1941 | Deep Hodge theory |
| `serre_gaga` | Serre, Ann. Inst. Fourier 6 (1956) | Large AG formalization |
| `harvey_lawson_theorem` | Harvey-Lawson, Acta Math. 148 (1982) | Deep GMT theorem |
| `harvey_lawson_represents` | Harvey-Lawson (1982) | Companion to above |
| `omega_pow_represents_multiple` | Classical AG | Hyperplane sections |

### ⚠️ INTERFACE AXIOMS (Engineering Layer)

These provide algebraic/smoothness properties and can remain until concrete definitions are chosen:

- `isSmoothAlternating_*` (5 axioms)
- `smoothExtDeriv_*` (2 axioms)
- `ofForm_*` (2 axioms)
- `instAddCommGroupDeRhamCohomologyClass`, `instModuleRealDeRhamCohomologyClass`
- Various `isClosed` axioms

### ❌ MUST BE PROVEN (Strategy-Critical)

These axioms likely encode the conjecture's hard content:

| Axiom | Why Critical |
|-------|--------------|
| `signed_decomposition` | Core decomposition step |
| `microstructureSequence_are_cycles` | Construction validity |
| `microstructureSequence_defect_bound` | Key estimate |
| `microstructureSequence_flat_limit_exists` | Compactness |
| `harvey_lawson_fundamental_class` | Representation bridge |
| `lefschetz_lift_signed_cycle` | Lefschetz compatibility |
| `limit_is_calibrated` | GMT limit property |
| `flat_limit_of_cycles_is_cycle` | GMT limit property |

---

## 📐 PROOF STRUCTURE OVERVIEW

The Hodge Conjecture proof has 3 main steps:

### Step 1: Signed Decomposition
Every rational Hodge class γ decomposes as:
$$\gamma = \gamma^+ - \gamma^-$$
where γ⁺ is cone-positive and γ⁻ = N·ω^p is already algebraic.

### Step 2: Automatic SYR (Microstructure)
For cone-positive γ⁺: build integral cycles T_k with calibration defect → 0.

### Step 3: Calibrated Limit → Algebraic
- Defect → 0 implies calibrated limit (Federer-Fleming)
- Calibrated = sum of analytic varieties (Harvey-Lawson)
- Analytic on projective = algebraic (GAGA)

---

## 📊 Current Axiom List

Reproduce with:
```bash
lake env lean DependencyCheck.lean
```

Current output (38 axioms):
```
'hodge_conjecture'' depends on axioms: [
  FundamentalClassSet_isClosed, IsAlgebraicSet, IsAlgebraicSet_empty,
  IsAlgebraicSet_union, calibration_inequality, exists_volume_form_of_submodule_axiom,
  flat_limit_of_cycles_is_cycle, hard_lefschetz_inverse_form,
  harvey_lawson_fundamental_class, harvey_lawson_represents, harvey_lawson_theorem,
  instAddCommGroupDeRhamCohomologyClass, instModuleRealDeRhamCohomologyClass,
  isClosed_omegaPow_scaled, isIntegral_zero_current, isSmoothAlternating_add,
  isSmoothAlternating_neg, isSmoothAlternating_smul, isSmoothAlternating_sub,
  isSmoothAlternating_zero, lefschetz_lift_signed_cycle, limit_is_calibrated,
  microstructureSequence_are_cycles, microstructureSequence_defect_bound,
  microstructureSequence_flat_limit_exists, ofForm_smul_real, ofForm_sub,
  omega_pow_isClosed, omega_pow_represents_multiple, propext, serre_gaga,
  signed_decomposition, simpleCalibratedForm_is_smooth, smoothExtDeriv_add,
  smoothExtDeriv_smul, wirtinger_comass_bound, Classical.choice, Quot.sound
]
```

---

## 📊 Sprint Overview

| Priority | Axioms | Est. Total LOC | Sprint Target |
|----------|--------|----------------|---------------|
| P0 (strategy-critical) | 6 | ~2,400 | Week 1-2 |
| P1 (GMT facts) | 2 | ~600 | Week 3 |
| **Total** | **8** | **~3,000** | **3 weeks** |

---

# 🤖 AGENT ASSIGNMENTS

## Agent Dependency Graph

```
                    ┌─────────────────────┐
                    │  Agent A: Signed    │
                    │   Decomposition     │
                    └─────────┬───────────┘
                              │
                              ▼
                    ┌─────────────────────┐
                    │  Agent B: Micro-    │
                    │  structure Core     │
                    └─────────┬───────────┘
                              │
              ┌───────────────┼───────────────┐
              ▼               ▼               ▼
    ┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐
    │  Agent C:       │ │  Agent D:       │ │  Agent E:       │
    │  Defect Bounds  │ │  GMT Limits     │ │  HL Bridge      │
    └─────────────────┘ └─────────────────┘ └─────────────────┘
```

---

# 🔷 AGENT A: Signed Decomposition

## Assignment

| Field | Value |
|-------|-------|
| **Axiom** | `signed_decomposition` |
| **Files** | `Hodge/Kahler/SignedDecomp.lean` |
| **Est. LOC** | 400-600 |
| **Target Date** | Week 1 |
| **Status** | 🔴 Not Started |

## Mission

Prove that every rational Hodge class γ can be written as γ = γ⁺ - γ⁻ where:
- γ⁺ is cone-positive (in the interior of the strongly positive cone)
- γ⁻ = N·ω^p for some rational N ≥ 0

## Current Code Location

```lean
-- Hodge/Kahler/SignedDecomp.lean:61
axiom signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (_h_hodge : isPPForm' n X p γ) (η : DeRhamCohomologyClass n X (2 * p)) 
    (h_rational : isRationalClass η) : SignedDecomposition γ h_closed
```

## Implementation Plan

### Step 1: Understand `SignedDecomposition` structure (lines 42-58)

```lean
structure SignedDecomposition {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ) where
  γplus : SmoothForm n X (2 * p)
  γminus : SmoothForm n X (2 * p)
  γplus_closed : IsFormClosed γplus
  γminus_closed : IsFormClosed γminus
  decomp : γ = γplus - γminus
  γplus_positive : isConePositive γplus
  γminus_rational : isRationalClass ⟦γminus, γminus_closed⟧
  γplus_rational : isRationalClass ⟦γplus, γplus_closed⟧
  γminus_is_omega_multiple : ∃ N : ℚ, ⟦γminus, γminus_closed⟧ = N • ⟦omegaPow n X p, omega_pow_isClosed p⟧
```

### Step 2: Key insight

Since ω^p is in the interior of the positive cone (from `omegaPow_in_interior`), for any bounded class γ, we can find N large enough so that γ + N·ω^p is also in the interior.

### Step 3: Required lemmas

```lean
-- 1. Norm bound on γ (compactness)
lemma rational_class_bounded {p : ℕ} (γ : SmoothForm n X (2 * p)) 
    (h_closed : IsFormClosed γ) (h_rational : isRationalClass ⟦γ, h_closed⟧) :
    ∃ M : ℝ, comass γ ≤ M

-- 2. Scaling preserves interior
lemma interior_scale_invariant {p : ℕ} (N : ℝ) (hN : N > 0) :
    isConePositive (N • omegaPow n X p)

-- 3. Addition into cone interior
lemma cone_interior_addition {p : ℕ} (α β : SmoothForm n X (2 * p))
    (hα : isConePositive α) (hβ_small : comass β < interior_radius α) :
    isConePositive (α + β)
```

## Deliverables

- [ ] Replace `axiom signed_decomposition` with `theorem signed_decomposition`
- [ ] Prove all helper lemmas above
- [ ] `lake build Hodge.Kahler.SignedDecomp` succeeds
- [ ] `#print axioms signed_decomposition` shows only allowed axioms

---

# 🔷 AGENT B: Microstructure Core

## Assignment

| Field | Value |
|-------|-------|
| **Axiom** | `microstructureSequence_are_cycles` |
| **Files** | `Hodge/Kahler/Microstructure.lean` |
| **Est. LOC** | 500-800 |
| **Target Date** | Week 1-2 |
| **Status** | 🔴 Not Started |

## Mission

Make `microstructureSequence` a concrete definition (not opaque) and prove that each element is a cycle (∂T_k = 0).

## Current Code Location

```lean
-- Hodge/Kahler/Microstructure.lean:211
opaque microstructureSequence (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ℕ → IntegralCurrent n X (2 * (n - p))

-- Hodge/Kahler/Microstructure.lean:228
axiom microstructureSequence_are_cycles (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, (microstructureSequence p γ hγ ψ k).isCycleAt
```

## Implementation Plan

### Step 1: Make the construction concrete

Replace `opaque microstructureSequence` with a `def`:

```lean
def microstructureSequence (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ℕ → IntegralCurrent n X (2 * (n - p)) := fun k =>
  let C := canonicalMeshSequence.cubulation k
  let h := canonicalMeshSequence.scale k
  let flow := calibratedFlow γ ψ C  -- Flow through each cell
  let int_flow := integerRounding flow  -- Round to integers
  let T_k := glueCells C int_flow  -- Glue integer cells together
  T_k
```

### Step 2: Key insight

Glued integer cells form closed chains because integer flows satisfy conservation (∑ inflow = ∑ outflow at each vertex). This is the discrete divergence-free condition.

### Step 3: Required infrastructure

```lean
-- Key lemma: glued cells are closed
lemma glueCells_isCycle (C : Cubulation n X h) (int_flow : DirectedEdge C → ℤ)
    (h_conserv : ∀ v, ∑ e ∈ inEdges v, int_flow e = ∑ e ∈ outEdges v, int_flow e) :
    (glueCells C int_flow).isCycleAt
```

## Deliverables

- [ ] Replace `opaque microstructureSequence` with concrete `def`
- [ ] Replace `axiom microstructureSequence_are_cycles` with `theorem`
- [ ] `lake build Hodge.Kahler.Microstructure` succeeds

---

# 🔷 AGENT C: Microstructure Bounds

## Assignment

| Field | Value |
|-------|-------|
| **Axioms** | `microstructureSequence_defect_bound`, `microstructureSequence_flat_limit_exists` |
| **Files** | `Hodge/Kahler/Microstructure.lean` |
| **Est. LOC** | 600-900 |
| **Target Date** | Week 2 |
| **Status** | 🔴 Not Started |
| **Depends on** | Agent B (microstructure construction) |

## Mission

Prove the calibration defect bound and the existence of a flat limit.

## Current Code Location

```lean
axiom microstructureSequence_defect_bound (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, calibrationDefect (microstructureSequence p γ hγ ψ k).toFun ψ ≤ 2 * (canonicalMeshSequence.scale k)

axiom microstructureSequence_flat_limit_exists (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_limit : IntegralCurrent n X (2 * (n - p))) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (fun j => flatNorm (...)) atTop (nhds 0)
```

## Implementation Plan

### Part 1: Defect Bound

- Defect comes from integer rounding error
- Each cell contributes error ≤ mesh^{2p}
- Net error = O(mesh) when properly weighted

### Part 2: Flat Limit Existence

1. Prove uniform mass bound: `∃ M, ∀ k, mass(T_k) ≤ M`
2. Apply Federer-Fleming compactness (can remain axiom)
3. Extract convergent subsequence

## Deliverables

- [ ] Replace both axioms with theorems
- [ ] `lake build Hodge.Kahler.Microstructure` succeeds

---

# 🔷 AGENT D: GMT Limit Properties

## Assignment

| Field | Value |
|-------|-------|
| **Axioms** | `limit_is_calibrated`, `flat_limit_of_cycles_is_cycle` |
| **Files** | `Hodge/Analytic/Calibration.lean`, `Hodge/Classical/HarveyLawson.lean` |
| **Est. LOC** | 400-600 |
| **Target Date** | Week 2-3 |
| **Status** | 🔴 Not Started |

## Mission

Prove the two GMT facts needed for the Harvey-Lawson theorem to apply.

## Current Code Location

```lean
-- Hodge/Analytic/Calibration.lean:93
axiom limit_is_calibrated {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k)
    (ψ : CalibratingForm n X k)
    (h_defect_vanish : Tendsto (fun i => calibrationDefect (T i) ψ) atTop (nhds 0))
    (h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    isCalibrated T_limit ψ

-- Hodge/Classical/HarveyLawson.lean:186
axiom flat_limit_of_cycles_is_cycle {k : ℕ}
    (T_seq : ℕ → IntegralCurrent n X k) (T_limit : IntegralCurrent n X k)
    (h_cycles : ∀ i, (T_seq i).isCycleAt)
    (h_conv : Tendsto (fun i => flatNorm (...)) atTop (nhds 0)) :
    T_limit.isCycleAt
```

## Implementation Plan

### Part 1: Calibrated Limits

Key lemmas needed:
- `mass_lsc_flat`: mass is lower semicontinuous in flat topology
- `pairing_continuous_flat`: pairing ⟨·, ψ⟩ is continuous in flat norm

Proof: Taking limits, mass(T_limit) ≤ liminf mass(T_i) = lim ⟨T_i, ψ⟩ = ⟨T_limit, ψ⟩. But mass ≥ pairing always, so equality holds.

### Part 2: Cycle Limits

Key lemma:
- `boundary_continuous_flat`: boundary is continuous in flat norm

Proof: ∂T_limit = lim ∂T_i = lim 0 = 0.

## Deliverables

- [ ] Replace both axioms with theorems
- [ ] `lake build Hodge.Analytic.Calibration` and `lake build Hodge.Classical.HarveyLawson` succeed

---

# 🔷 AGENT E: Harvey-Lawson Bridge

## Assignment

| Field | Value |
|-------|-------|
| **Axioms** | `harvey_lawson_fundamental_class`, `lefschetz_lift_signed_cycle` |
| **Files** | `Hodge/Kahler/Main.lean` |
| **Est. LOC** | 500-700 |
| **Target Date** | Week 3 |
| **Status** | 🔴 Not Started |
| **Depends on** | Agents C, D |

## Mission

Prove the cohomology-level bridges that complete the proof.

## Current Code Location

```lean
axiom harvey_lawson_fundamental_class {p : ℕ}
    (γplus : SmoothForm n X (2 * p)) (hplus : IsFormClosed γplus)
    (hγ : isConePositive γplus)
    (hl_concl : HarveyLawsonConclusion n X (2 * (n - p)))
    (T_limit : Current n X (2 * (n - p)))
    (h_represents : hl_concl.represents T_limit) :
    hl_concl.toSignedAlgebraicCycle.RepresentsClass (DeRhamCohomologyClass.ofForm γplus hplus)

axiom lefschetz_lift_signed_cycle {p p' : ℕ}
    (γ : SmoothForm n X (2 * p)) (hγ : IsFormClosed γ)
    (η : SmoothForm n X (2 * p')) (hη : IsFormClosed η)
    (Z_η : SignedAlgebraicCycle n X)
    (hp : p > n / 2)
    (h_rep : Z_η.RepresentsClass (DeRhamCohomologyClass.ofForm η hη)) :
    ∃ Z_γ : SignedAlgebraicCycle n X, 
      Z_γ.RepresentsClass (DeRhamCohomologyClass.ofForm γ hγ)
```

## Implementation Plan

### Part 1: Harvey-Lawson Fundamental Class

Chain of representations:
```
γplus (form) 
  ↓ (microstructure construction)
T_k (integral currents)
  ↓ (flat limit)
T_limit (calibrated current)
  ↓ (Harvey-Lawson theorem)
∑ n_i [V_i] (analytic varieties)
  ↓ (GAGA)
∑ n_i [W_i] (algebraic varieties)
  ↓ (fundamental class)
[Z] (cohomology class) = [γplus]
```

### Part 2: Lefschetz Lift

- L^{p-p'} : H^{p',p'} → H^{p,p} is isomorphism (Hard Lefschetz)
- At cycle level: Z_γ = Z_η ∩ H^{p-p'} (hyperplane sections)
- Cycle class commutes with Lefschetz

## Deliverables

- [ ] Replace both axioms with theorems
- [ ] `lake build Hodge.Kahler.Main` succeeds

---

# 📊 Agent Summary

| Agent | Axiom(s) | Est. LOC | Week | Dependencies |
|-------|----------|----------|------|--------------|
| **A** | `signed_decomposition` | 500 | 1 | None |
| **B** | `microstructureSequence_are_cycles` | 650 | 1-2 | None |
| **C** | `*_defect_bound`, `*_flat_limit_exists` | 750 | 2 | Agent B |
| **D** | `limit_is_calibrated`, `flat_limit_of_cycles_is_cycle` | 500 | 2-3 | None |
| **E** | `harvey_lawson_fundamental_class`, `lefschetz_lift_signed_cycle` | 600 | 3 | Agents C, D |
| **TOTAL** | 8 axioms | ~3,000 | 3 weeks | |

---

# ✅ Definition of Done

An axiom is considered "complete" when:

1. [ ] The `axiom` keyword is replaced with `theorem` or `def`
2. [ ] The proof compiles without `sorry`
3. [ ] `lake build` passes
4. [ ] `#print axioms hodge_conjecture'` no longer lists this axiom
5. [ ] Code review passed

---

# 📈 Progress Tracker

| Axiom | Est. LOC | Actual LOC | Status | Assignee |
|-------|----------|------------|--------|----------|
| signed_decomposition | 500 | - | 🔴 | - |
| microstructureSequence_are_cycles | 650 | - | 🔴 | - |
| microstructureSequence_defect_bound | 400 | - | 🔴 | - |
| microstructureSequence_flat_limit_exists | 500 | - | 🔴 | - |
| harvey_lawson_fundamental_class | 300 | - | 🔴 | - |
| lefschetz_lift_signed_cycle | 400 | - | 🔴 | - |
| limit_is_calibrated | 300 | - | 🔴 | - |
| flat_limit_of_cycles_is_cycle | 300 | - | 🔴 | - |
| **TOTAL** | **3,350** | - | - | - |

---

# 📋 Copy-Paste Agent Prompts

Use these prompts to assign agents to work on specific axioms.

## Agent A Prompt

```
You are working on the Hodge Conjecture Lean formalization.

**Your assignment:** Convert `signed_decomposition` from an axiom to a theorem.

**File:** `Hodge/Kahler/SignedDecomp.lean:61`

**Current axiom:**
axiom signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (_h_hodge : isPPForm' n X p γ) (η : DeRhamCohomologyClass n X (2 * p)) 
    (h_rational : isRationalClass η) : SignedDecomposition γ h_closed

**What to prove:**
Given a rational Hodge class γ, construct γ = γ⁺ - γ⁻ where:
- γ⁺ is cone-positive (in the interior of the strongly positive cone)  
- γ⁻ = N·ω^p for some rational N ≥ 0

**Key insight:** Since ω^p is in the interior of the positive cone (`omegaPow_in_interior`), for any bounded class γ, find N large enough so that γ + N·ω^p is cone-positive.

**Rules:**
- NO `sorry`, `admit`, or placeholders
- Search Mathlib first before writing custom proofs
- Build incrementally: `lake build Hodge.Kahler.SignedDecomp`

**Deliverable:** Replace `axiom` with `theorem` and provide a complete proof.
```

## Agent B Prompt

```
You are working on the Hodge Conjecture Lean formalization.

**Your assignment:** Make `microstructureSequence` concrete and prove each element is a cycle.

**File:** `Hodge/Kahler/Microstructure.lean:211-230`

**Current code:**
opaque microstructureSequence (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ℕ → IntegralCurrent n X (2 * (n - p))

axiom microstructureSequence_are_cycles (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, (microstructureSequence p γ hγ ψ k).isCycleAt

**What to do:**
1. Replace `opaque microstructureSequence` with a concrete `def`
2. Prove `microstructureSequence_are_cycles` as a theorem
3. The construction uses: cubulation → calibrated flow → integer rounding → gluing

**Key insight:** Glued integer cells form closed chains because integer flows satisfy conservation (∑ inflow = ∑ outflow at each vertex).

**Rules:**
- NO `sorry`, `admit`, or placeholders
- Build incrementally: `lake build Hodge.Kahler.Microstructure`

**Deliverable:** Concrete definition + theorem proving ∂T_k = 0 for each approximant.
```

## Agent C Prompt

```
You are working on the Hodge Conjecture Lean formalization.

**Your assignment:** Prove the calibration defect bound and flat limit existence.

**File:** `Hodge/Kahler/Microstructure.lean:234-274`

**Depends on:** Agent B must complete `microstructureSequence` definition first.

**Current axioms:**
axiom microstructureSequence_defect_bound (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, calibrationDefect (microstructureSequence p γ hγ ψ k).toFun ψ ≤ 2 * (canonicalMeshSequence.scale k)

axiom microstructureSequence_flat_limit_exists (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_limit : IntegralCurrent n X (2 * (n - p))) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (fun j => flatNorm (...)) atTop (nhds 0)

**What to prove:**
1. Defect bound: integer rounding error is O(mesh size)
2. Mass bound: uniform bound on mass(T_k)
3. Flat limit: apply Federer-Fleming compactness (can stay as axiom)

**Rules:**
- NO `sorry`, `admit`, or placeholders
- Build: `lake build Hodge.Kahler.Microstructure`

**Deliverable:** Both axioms converted to theorems.
```

## Agent D Prompt

```
You are working on the Hodge Conjecture Lean formalization.

**Your assignment:** Prove the two GMT limit facts needed for Harvey-Lawson.

**Files:** 
- `Hodge/Analytic/Calibration.lean:93`
- `Hodge/Classical/HarveyLawson.lean:186`

**Current axioms:**
axiom limit_is_calibrated {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k)
    (ψ : CalibratingForm n X k)
    (h_defect_vanish : Tendsto (fun i => calibrationDefect (T i) ψ) atTop (nhds 0))
    (h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    isCalibrated T_limit ψ

axiom flat_limit_of_cycles_is_cycle {k : ℕ}
    (T_seq : ℕ → IntegralCurrent n X k) (T_limit : IntegralCurrent n X k)
    (h_cycles : ∀ i, (T_seq i).isCycleAt)
    (h_conv : Tendsto (fun i => flatNorm (...)) atTop (nhds 0)) :
    T_limit.isCycleAt

**What to prove:**
1. `limit_is_calibrated`: Use mass lower semicontinuity + pairing continuity
2. `flat_limit_of_cycles_is_cycle`: Use boundary continuity in flat norm

**Key lemmas needed:**
- `mass_lsc_flat`: mass is lower semicontinuous in flat topology
- `boundary_continuous_flat`: boundary is continuous in flat norm

**Rules:**
- NO `sorry`, `admit`, or placeholders
- Build: `lake build Hodge.Analytic.Calibration` and `lake build Hodge.Classical.HarveyLawson`

**Deliverable:** Both axioms converted to theorems.
```

## Agent E Prompt

```
You are working on the Hodge Conjecture Lean formalization.

**Your assignment:** Prove the cohomology-level bridges completing the proof.

**File:** `Hodge/Kahler/Main.lean:94-155`

**Depends on:** Agents C and D must complete their axioms first.

**Current axioms:**
axiom harvey_lawson_fundamental_class {p : ℕ}
    (γplus : SmoothForm n X (2 * p)) (hplus : IsFormClosed γplus)
    (hγ : isConePositive γplus) (hl_concl : HarveyLawsonConclusion n X (2 * (n - p)))
    (T_limit : Current n X (2 * (n - p))) (h_represents : hl_concl.represents T_limit) :
    hl_concl.toSignedAlgebraicCycle.RepresentsClass (DeRhamCohomologyClass.ofForm γplus hplus)

axiom lefschetz_lift_signed_cycle {p p' : ℕ}
    (γ : SmoothForm n X (2 * p)) (hγ : IsFormClosed γ) ...
    (hp : p > n / 2) (h_rep : Z_η.RepresentsClass ...) :
    ∃ Z_γ : SignedAlgebraicCycle n X, Z_γ.RepresentsClass (DeRhamCohomologyClass.ofForm γ hγ)

**What to prove:**
1. `harvey_lawson_fundamental_class`: Chain of representations (microstructure → limit → HL → GAGA → fundamental class)
2. `lefschetz_lift_signed_cycle`: Cycle classes commute with Lefschetz operator

**Rules:**
- NO `sorry`, `admit`, or placeholders  
- Keep `harvey_lawson_theorem`, `serre_gaga`, `hard_lefschetz_inverse_form` as axioms
- Build: `lake build Hodge.Kahler.Main`

**Deliverable:** Both axioms converted to theorems.
```

---

# 🔗 Related Documents

- `HodgeAxiomCompletionRoadmap.pdf` — Formatted version for circulation
- `LeanProofBundle.txt` — Full codebase bundle for reference
- `ADVERSARIAL_AUDIT.md` — Audit findings and status
- `Hodge-v6-w-Jon-Update-MERGED.tex` — Mathematical paper
