# Axiom Completion Sprint

**Generated:** 2024-12-30  
**Goal:** Eliminate strategy-critical axioms to make the Hodge proof solid  
**Current axiom count:** 38  
**Target axiom count:** ~30 (remove 8 strategy-critical axioms)

---

## 📊 Sprint Overview

| Priority | Axioms | Est. Total LOC | Sprint Target |
|----------|--------|----------------|---------------|
| P0 (strategy-critical) | 6 | ~2,400 | Week 1-2 |
| P1 (GMT facts) | 2 | ~600 | Week 3 |
| **Total** | **8** | **~3,000** | **3 weeks** |

---

## 🔴 P0: Strategy-Critical Axioms (MUST COMPLETE)

These axioms likely encode the conjecture's hard content. Completing them ensures the proof doesn't assume the core bridge.

### 1. `signed_decomposition`

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Kahler/SignedDecomp.lean:61` |
| **Est. LOC** | 400-600 |
| **Difficulty** | ⭐⭐⭐⭐ (Hard) |
| **Dependencies** | `isRationalClass`, `isConePositive`, cone geometry |
| **Blocking** | Everything downstream |

**Current signature:**
```lean
axiom signed_decomposition {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (_h_hodge : isPPForm' n X p γ) (η : DeRhamCohomologyClass n X (2 * p)) 
    (h_rational : isRationalClass η) : SignedDecomposition γ h_closed
```

**What needs to be proved:**
- Given a rational Hodge class γ, decompose it as γ = γ⁺ - γ⁻
- γ⁺ must be cone-positive (in the interior of strongly positive cone)
- γ⁻ = N·ω^p for some rational N (already algebraic)
- Both must preserve closedness and rationality

**Approach:**
1. Use that ω^p is in the interior of the positive cone
2. For rational γ, find N large enough so that γ + N·ω^p is cone-positive
3. Set γ⁺ = γ + N·ω^p, γ⁻ = N·ω^p

**Assigned to:** `___________`

---

### 2. `microstructureSequence_are_cycles`

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Kahler/Microstructure.lean:228` |
| **Est. LOC** | 500-800 |
| **Difficulty** | ⭐⭐⭐⭐⭐ (Very Hard) |
| **Dependencies** | Cubulation, Flow, IntegralCurrent |
| **Blocking** | Defect bound, flat limit |

**Current signature:**
```lean
axiom microstructureSequence_are_cycles (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, (microstructureSequence p γ hγ ψ k).isCycleAt
```

**What needs to be proved:**
- Define `microstructureSequence` as a concrete construction (not opaque)
- Each approximant T_k must satisfy ∂T_k = 0
- Use cubulation + integer rounding + gluing

**Approach:**
1. First make `microstructureSequence` a `def` not `opaque`
2. Prove boundary vanishes by construction (closed polyhedral chains)
3. Use `boundary_boundary` = 0 and careful bookkeeping

**Assigned to:** `___________`

---

### 3. `microstructureSequence_defect_bound`

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Kahler/Microstructure.lean:234` |
| **Est. LOC** | 300-500 |
| **Difficulty** | ⭐⭐⭐⭐ (Hard) |
| **Dependencies** | `microstructureSequence_are_cycles`, calibrationDefect |
| **Blocking** | `limit_is_calibrated` |

**Current signature:**
```lean
axiom microstructureSequence_defect_bound (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, calibrationDefect (microstructureSequence p γ hγ ψ k).toFun ψ ≤ 2 * (canonicalMeshSequence.scale k)
```

**What needs to be proved:**
- The calibration defect is bounded by O(mesh size)
- As mesh → 0, defect → 0

**Approach:**
1. Defect comes from integer rounding error
2. Error per cell is O(mesh^{2p})
3. Number of cells is O(mesh^{-2n})
4. Total defect = O(mesh^{2p-2n}) · mass = O(mesh) when properly scaled

**Assigned to:** `___________`

---

### 4. `microstructureSequence_flat_limit_exists`

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Kahler/Microstructure.lean:269` |
| **Est. LOC** | 400-600 |
| **Difficulty** | ⭐⭐⭐⭐ (Hard) |
| **Dependencies** | Mass bound, Federer-Fleming compactness |
| **Blocking** | Harvey-Lawson application |

**Current signature:**
```lean
axiom microstructureSequence_flat_limit_exists (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_limit : IntegralCurrent n X (2 * (n - p))) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Filter.Tendsto (fun j => flatNorm ((microstructureSequence p γ hγ ψ (φ j)).toFun - T_limit.toFun))
        Filter.atTop (nhds 0)
```

**What needs to be proved:**
- The microstructure sequence has uniformly bounded mass
- By Federer-Fleming compactness, extract convergent subsequence
- Limit exists in flat norm topology

**Approach:**
1. Prove `microstructureSequence_mass_bound` (uniform mass bound)
2. Apply Federer-Fleming compactness (can remain an axiom)
3. Extract subsequence φ and limit T_limit

**Assigned to:** `___________`

---

### 5. `harvey_lawson_fundamental_class`

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Kahler/Main.lean:94` |
| **Est. LOC** | 200-400 |
| **Difficulty** | ⭐⭐⭐ (Medium) |
| **Dependencies** | FundamentalClass, HarveyLawsonConclusion |
| **Blocking** | Final representation |

**Current signature:**
```lean
axiom harvey_lawson_fundamental_class {p : ℕ}
    (γplus : SmoothForm n X (2 * p)) (hplus : IsFormClosed γplus)
    (hγ : isConePositive γplus)
    (hl_concl : HarveyLawsonConclusion n X (2 * (n - p)))
    (T_limit : Current n X (2 * (n - p)))
    (h_represents : hl_concl.represents T_limit) :
    hl_concl.toSignedAlgebraicCycle.RepresentsClass (DeRhamCohomologyClass.ofForm γplus hplus)
```

**What needs to be proved:**
- The Harvey-Lawson output (analytic → algebraic cycle) represents γ⁺
- This is the cohomology-level identification

**Approach:**
1. The limit T_limit represents γ⁺ by construction (integration)
2. HL says T_limit = sum of analytic subvarieties
3. GAGA converts analytic → algebraic
4. Fundamental class of algebraic cycle = original class

**Assigned to:** `___________`

---

### 6. `lefschetz_lift_signed_cycle`

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Kahler/Main.lean:150` |
| **Est. LOC** | 300-500 |
| **Difficulty** | ⭐⭐⭐ (Medium) |
| **Dependencies** | Hard Lefschetz, cycle class maps |
| **Blocking** | Cases p > n/2 |

**Current signature:**
```lean
axiom lefschetz_lift_signed_cycle {p p' : ℕ}
    (γ : SmoothForm n X (2 * p)) (hγ : IsFormClosed γ)
    (η : SmoothForm n X (2 * p')) (hη : IsFormClosed η)
    (Z_η : SignedAlgebraicCycle n X)
    (_hp : p > n / 2)
    (h_rep : Z_η.RepresentsClass (DeRhamCohomologyClass.ofForm η hη)) :
    ∃ Z_γ : SignedAlgebraicCycle n X, 
      Z_γ.RepresentsClass (DeRhamCohomologyClass.ofForm γ hγ)
```

**What needs to be proved:**
- If p > n/2, use Hard Lefschetz to reduce to p' ≤ n/2
- Cycle classes compatible with hyperplane intersection
- Lift back from p' to p

**Approach:**
1. L^{p-n/2} : H^{p',p'} → H^{p,p} is isomorphism (Hard Lefschetz)
2. At cycle level: Z_γ = Z_η ∩ H^{p-p'} (hyperplane sections)
3. Prove cycle class map commutes with Lefschetz L

**Assigned to:** `___________`

---

## 🟡 P1: Pipeline Integrity (GMT Facts)

Standard GMT facts that complete the analytic pipeline.

### 7. `limit_is_calibrated`

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Analytic/Calibration.lean:93` |
| **Est. LOC** | 200-400 |
| **Difficulty** | ⭐⭐⭐ (Medium) |
| **Dependencies** | Lower semicontinuity of mass, calibration inequality |
| **Blocking** | Harvey-Lawson hypothesis |

**Current signature:**
```lean
axiom limit_is_calibrated {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k)
    (ψ : CalibratingForm n X k)
    (_h_defect_vanish : Tendsto (fun i => calibrationDefect (T i) ψ) atTop (nhds 0))
    (_h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    isCalibrated T_limit ψ
```

**What needs to be proved:**
- If calibration defect → 0 and T_i → T_limit in flat norm
- Then T_limit is calibrated

**Approach:**
1. Calibration defect = |mass(T) - ⟨T, ψ⟩|
2. Mass is lower semicontinuous in flat topology
3. Pairing ⟨·, ψ⟩ is continuous in flat topology
4. Taking limits: defect(T_limit) ≤ liminf defect(T_i) = 0

**Assigned to:** `___________`

---

### 8. `flat_limit_of_cycles_is_cycle`

| Field | Value |
|-------|-------|
| **Location** | `Hodge/Classical/HarveyLawson.lean:186` |
| **Est. LOC** | 200-400 |
| **Difficulty** | ⭐⭐⭐ (Medium) |
| **Dependencies** | Boundary continuity in flat norm |
| **Blocking** | Harvey-Lawson hypothesis |

**Current signature:**
```lean
axiom flat_limit_of_cycles_is_cycle {k : ℕ}
    (T_seq : ℕ → IntegralCurrent n X k)
    (T_limit : IntegralCurrent n X k)
    (h_cycles : ∀ i, (T_seq i).isCycleAt)
    (h_conv : Filter.Tendsto (fun i => flatNorm ((T_seq i).toFun - T_limit.toFun))
              Filter.atTop (nhds 0)) :
    T_limit.isCycleAt
```

**What needs to be proved:**
- If T_i → T_limit in flat norm and each ∂T_i = 0
- Then ∂T_limit = 0

**Approach:**
1. Boundary operator ∂ is continuous in flat norm
2. ∂T_i = 0 for all i
3. ∂T_limit = lim ∂T_i = lim 0 = 0

**Assigned to:** `___________`

---

## 📋 Assignment Template

Copy this for each agent assignment:

```markdown
## Assignment: [AXIOM_NAME]

**Agent:** [Agent ID]  
**Start Date:** YYYY-MM-DD  
**Target Date:** YYYY-MM-DD  
**Status:** 🔴 Not Started / 🟡 In Progress / 🟢 Complete

### Files to modify:
- [ ] `Hodge/[path].lean`

### Subtasks:
- [ ] Task 1
- [ ] Task 2
- [ ] Task 3

### Blockers:
- None

### Notes:
```

---

## 🗓️ Sprint Schedule

| Week | Focus | Axioms | Est. LOC |
|------|-------|--------|----------|
| 1 | Signed decomposition + Microstructure setup | 1, 2 | 1,000 |
| 2 | Microstructure bounds + Limit existence | 3, 4 | 800 |
| 3 | HL bridge + GMT limits | 5, 6, 7, 8 | 1,200 |

---

## 📈 Progress Tracker

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

## ✅ Definition of Done

An axiom is considered "complete" when:

1. [ ] The `axiom` keyword is replaced with `theorem` or `def`
2. [ ] The proof compiles without `sorry`
3. [ ] `lake build` passes
4. [ ] `#print axioms hodge_conjecture'` no longer lists this axiom
5. [ ] Code review passed

---

## 🔗 Related Documents

- `AGENT_ASSIGNMENTS.md` — Full agent assignment protocol
- `ADVERSARIAL_AUDIT.md` — Audit findings and status
- `HodgeAxiomCompletionRoadmap.pdf` — Formatted version of this document
- `LeanProofBundle.txt` — Full codebase bundle for reference

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

This is the key decomposition that enables the microstructure construction.

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

### Step 2: Prove the decomposition theorem

**Key insight:** Since ω^p is in the interior of the cone (from `omegaPow_in_interior`), for any bounded class γ, we can find N large enough so that γ + N·ω^p is also in the interior.

```lean
theorem signed_decomposition_proof {p : ℕ} (γ : SmoothForm n X (2 * p)) 
    (h_closed : IsFormClosed γ) (h_hodge : isPPForm' n X p γ) 
    (η : DeRhamCohomologyClass n X (2 * p)) (h_rational : isRationalClass η) : 
    SignedDecomposition γ h_closed := by
  -- Step 1: ω^p is in the interior of the positive cone
  have h_omega_interior := omegaPow_in_interior (n := n) (X := X) p
  
  -- Step 2: Get the interior radius r > 0
  obtain ⟨r, hr_pos, hr_ball⟩ := exists_uniform_interior_radius (n := n) (X := X) p
  
  -- Step 3: γ is bounded (uses compactness of X)
  -- Need: ‖γ‖ ≤ M for some M
  
  -- Step 4: Choose N = ⌈M/r⌉ + 1 (rational)
  -- Then γ + N·ω^p is in the r-ball around N·ω^p
  -- Since N·ω^p is deep in the cone, γ + N·ω^p is cone-positive
  
  -- Step 5: Construct the decomposition
  -- γplus := γ + N·ω^p
  -- γminus := N·ω^p
  -- Verify all conditions
  sorry
```

### Step 3: Required lemmas

You'll need to prove these helper lemmas:

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

-- 4. Rationality preserved under addition
lemma isRationalClass_add_omega_multiple {p : ℕ} (γ : SmoothForm n X (2 * p))
    (h_closed : IsFormClosed γ) (h_rational : isRationalClass ⟦γ, h_closed⟧) (N : ℚ) :
    isRationalClass ⟦γ + N • omegaPow n X p, _⟧
```

## Deliverables

- [ ] Replace `axiom signed_decomposition` with `theorem signed_decomposition`
- [ ] Prove all 4 helper lemmas above
- [ ] `lake build Hodge.Kahler.SignedDecomp` succeeds
- [ ] `#print axioms signed_decomposition` shows only allowed axioms

## Blockers

- Needs `omegaPow_in_interior` (already an axiom, acceptable)
- Needs `exists_uniform_interior_radius` (already an axiom, acceptable)

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
/-- The microstructure sequence: integral current approximants to γ. -/
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

### Step 2: Prove each approximant is a cycle

```lean
theorem microstructureSequence_are_cycles_proof (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, (microstructureSequence p γ hγ ψ k).isCycleAt := by
  intro k
  unfold microstructureSequence
  -- The glued cells form a closed chain
  -- Key: integer flows satisfy ∑ (inflow) = ∑ (outflow) at each vertex
  -- This is the discrete divergence-free condition
  -- Therefore ∂(glued chain) = 0
  sorry
```

### Step 3: Required infrastructure

```lean
-- 1. Cubulation structure (already exists)
structure Cubulation (n : ℕ) (X : Type*) (h : ℝ) where ...

-- 2. Flow through cells
def calibratedFlow (γ : SmoothForm n X (2 * p)) (ψ : CalibratingForm n X (2 * (n - p)))
    (C : Cubulation n X h) : DirectedEdge C → ℝ := ...

-- 3. Integer rounding with conservation
def integerRounding (flow : DirectedEdge C → ℝ) : DirectedEdge C → ℤ := ...

-- 4. Gluing cells into a current
def glueCells (C : Cubulation n X h) (int_flow : DirectedEdge C → ℤ) : 
    IntegralCurrent n X (2 * (n - p)) := ...

-- 5. Key lemma: glued cells are closed
lemma glueCells_isCycle (C : Cubulation n X h) (int_flow : DirectedEdge C → ℤ)
    (h_conserv : ∀ v, ∑ e ∈ inEdges v, int_flow e = ∑ e ∈ outEdges v, int_flow e) :
    (glueCells C int_flow).isCycleAt
```

### Step 4: Integer rounding with flow conservation

The key mathematical insight: use the Barany-Grinberg theorem for integer rounding that preserves flow conservation.

```lean
-- Already have this axiom:
axiom integer_transport (p : ℕ) {h : ℝ} (C : Cubulation n X h) (target : Flow C) :
    ∃ (int_flow : DirectedEdge C → ℤ), IsValidIntegerApproximation C target int_flow
```

## Deliverables

- [ ] Replace `opaque microstructureSequence` with concrete `def`
- [ ] Replace `axiom microstructureSequence_are_cycles` with `theorem`
- [ ] Define `calibratedFlow`, `integerRounding`, `glueCells`
- [ ] Prove `glueCells_isCycle` lemma
- [ ] `lake build Hodge.Kahler.Microstructure` succeeds

## Blockers

- Needs `Cubulation` structure (exists)
- Needs `integer_transport` axiom (keep as axiom for Barany-Grinberg)

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
-- Hodge/Kahler/Microstructure.lean:234
axiom microstructureSequence_defect_bound (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, calibrationDefect (microstructureSequence p γ hγ ψ k).toFun ψ ≤ 2 * (canonicalMeshSequence.scale k)

-- Hodge/Kahler/Microstructure.lean:269
axiom microstructureSequence_flat_limit_exists (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_limit : IntegralCurrent n X (2 * (n - p))) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Filter.Tendsto (fun j => flatNorm ((microstructureSequence p γ hγ ψ (φ j)).toFun - T_limit.toFun))
        Filter.atTop (nhds 0)
```

## Implementation Plan

### Part 1: Defect Bound

```lean
theorem microstructureSequence_defect_bound_proof (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∀ k, calibrationDefect (microstructureSequence p γ hγ ψ k).toFun ψ ≤ 
         2 * (canonicalMeshSequence.scale k) := by
  intro k
  -- Step 1: Defect comes from integer rounding error
  -- Each cell contributes error ≤ mesh^{2p} (local rounding)
  
  -- Step 2: Number of cells is O(mesh^{-2n})
  
  -- Step 3: But errors partially cancel (by calibration)
  -- Net error = O(mesh) when properly weighted
  
  sorry
```

**Key lemmas needed:**

```lean
-- Per-cell defect bound
lemma cell_defect_bound (C : Cubulation n X h) (cell : Cell C) 
    (int_flow : DirectedEdge C → ℤ) (real_flow : DirectedEdge C → ℝ) :
    cellDefect cell int_flow ψ ≤ h^(2*p) * ‖real_flow - int_flow‖_cell

-- Cancellation from calibration form
lemma calibration_cancellation (C : Cubulation n X h) (int_flow : DirectedEdge C → ℤ) :
    ∑ cell, cellDefect cell int_flow ψ ≤ C_const * h * mass(glueCells C int_flow)
```

### Part 2: Flat Limit Existence

```lean
theorem microstructureSequence_flat_limit_exists_proof (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_limit : IntegralCurrent n X (2 * (n - p))) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Filter.Tendsto (fun j => flatNorm ((microstructureSequence p γ hγ ψ (φ j)).toFun - T_limit.toFun))
        Filter.atTop (nhds 0) := by
  -- Step 1: Prove uniform mass bound
  have h_mass_bound := microstructureSequence_mass_bound p γ hγ ψ
  obtain ⟨M, hM⟩ := h_mass_bound
  
  -- Step 2: Apply Federer-Fleming compactness (axiom)
  -- Bounded mass + bounded support → precompact in flat norm
  
  -- Step 3: Extract convergent subsequence
  sorry
```

**Key: first prove mass bound**

```lean
theorem microstructureSequence_mass_bound_proof (p : ℕ) (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ M : ℝ, ∀ k, (microstructureSequence p γ hγ ψ k : Current n X (2 * (n - p))).mass ≤ M := by
  -- Mass of T_k ≈ ∫_X γ ∧ ψ (by calibration)
  -- This is bounded since γ, ψ are fixed smooth forms on compact X
  use comass γ * comass ψ * volume X
  intro k
  sorry
```

## Deliverables

- [ ] Replace `axiom microstructureSequence_defect_bound` with `theorem`
- [ ] Replace `axiom microstructureSequence_flat_limit_exists` with `theorem`  
- [ ] Prove `microstructureSequence_mass_bound` as intermediate
- [ ] Prove cell-level defect estimates
- [ ] `lake build Hodge.Kahler.Microstructure` succeeds

## Blockers

- **Depends on Agent B:** needs concrete `microstructureSequence` definition
- Keep `federer_fleming_compactness` as axiom (deep GMT theorem)

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

Prove the two GMT facts needed for the Harvey-Lawson theorem to apply:
1. Flat limits of nearly-calibrated currents are calibrated
2. Flat limits of cycles are cycles

## Current Code Location

```lean
-- Hodge/Analytic/Calibration.lean:93
axiom limit_is_calibrated {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k)
    (ψ : CalibratingForm n X k)
    (_h_defect_vanish : Tendsto (fun i => calibrationDefect (T i) ψ) atTop (nhds 0))
    (_h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    isCalibrated T_limit ψ

-- Hodge/Classical/HarveyLawson.lean:186
axiom flat_limit_of_cycles_is_cycle {k : ℕ}
    (T_seq : ℕ → IntegralCurrent n X k)
    (T_limit : IntegralCurrent n X k)
    (h_cycles : ∀ i, (T_seq i).isCycleAt)
    (h_conv : Filter.Tendsto (fun i => flatNorm ((T_seq i).toFun - T_limit.toFun))
              Filter.atTop (nhds 0)) :
    T_limit.isCycleAt
```

## Implementation Plan

### Part 1: Calibrated Limits

```lean
theorem limit_is_calibrated_proof {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k)
    (ψ : CalibratingForm n X k)
    (h_defect_vanish : Tendsto (fun i => calibrationDefect (T i) ψ) atTop (nhds 0))
    (h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    isCalibrated T_limit ψ := by
  -- Recall: isCalibrated T ψ ↔ mass T = ⟨T, ψ⟩
  -- Equivalently: calibrationDefect T ψ = |mass T - ⟨T, ψ⟩| = 0
  
  -- Step 1: mass is lower semicontinuous in flat norm
  have h_mass_lsc : mass T_limit ≤ liminf (fun i => mass (T i)) := mass_lsc_flat h_conv
  
  -- Step 2: pairing ⟨·, ψ⟩ is continuous in flat norm
  have h_pair_cont : Tendsto (fun i => ⟨T i, ψ⟩) atTop (nhds ⟨T_limit, ψ⟩) := 
    pairing_continuous_flat h_conv ψ
  
  -- Step 3: By defect → 0, we have mass(T_i) → ⟨T_i, ψ⟩
  -- Taking limits: mass(T_limit) ≤ liminf mass(T_i) = lim ⟨T_i, ψ⟩ = ⟨T_limit, ψ⟩
  
  -- Step 4: But always mass(T) ≥ ⟨T, ψ⟩ (calibration inequality)
  -- So mass(T_limit) = ⟨T_limit, ψ⟩, i.e., T_limit is calibrated
  
  sorry
```

**Key lemmas:**

```lean
-- Lower semicontinuity of mass (standard GMT)
lemma mass_lsc_flat {T_seq : ℕ → Current n X k} {T_limit : Current n X k}
    (h_conv : Tendsto (fun i => flatNorm (T_seq i - T_limit)) atTop (nhds 0)) :
    mass T_limit ≤ liminf (fun i => mass (T_seq i))

-- Pairing is continuous in flat norm (because ψ is smooth)
lemma pairing_continuous_flat {T_seq : ℕ → Current n X k} {T_limit : Current n X k}
    (h_conv : Tendsto (fun i => flatNorm (T_seq i - T_limit)) atTop (nhds 0))
    (ψ : SmoothForm n X k) :
    Tendsto (fun i => T_seq i ψ) atTop (nhds (T_limit ψ))
```

### Part 2: Cycle Limits

```lean
theorem flat_limit_of_cycles_is_cycle_proof {k : ℕ}
    (T_seq : ℕ → IntegralCurrent n X k)
    (T_limit : IntegralCurrent n X k)
    (h_cycles : ∀ i, (T_seq i).isCycleAt)
    (h_conv : Filter.Tendsto (fun i => flatNorm ((T_seq i).toFun - T_limit.toFun))
              Filter.atTop (nhds 0)) :
    T_limit.isCycleAt := by
  -- isCycleAt means boundary T = 0
  
  -- Step 1: Boundary is continuous in flat norm
  have h_bdy_cont : Tendsto (fun i => boundary (T_seq i).toFun) atTop 
                           (nhds (boundary T_limit.toFun)) := 
    boundary_continuous_flat h_conv
  
  -- Step 2: Each T_seq i is a cycle, so boundary (T_seq i) = 0
  have h_bdy_zero : ∀ i, boundary (T_seq i).toFun = 0 := fun i => (h_cycles i).boundary_eq_zero
  
  -- Step 3: Taking limits: boundary T_limit = lim boundary (T_seq i) = lim 0 = 0
  have h_limit_zero : boundary T_limit.toFun = 0 := by
    have := tendsto_const_nhds (x := (0 : Current n X (k-1)))
    rw [show (fun i => boundary (T_seq i).toFun) = (fun _ => 0) from funext h_bdy_zero] at h_bdy_cont
    exact tendsto_nhds_unique h_bdy_cont this
  
  exact ⟨h_limit_zero⟩
```

**Key lemma:**

```lean
-- Boundary is continuous in flat norm
lemma boundary_continuous_flat {T_seq : ℕ → Current n X k} {T_limit : Current n X k}
    (h_conv : Tendsto (fun i => flatNorm (T_seq i - T_limit)) atTop (nhds 0)) :
    Tendsto (fun i => boundary (T_seq i)) atTop (nhds (boundary T_limit))
```

This follows from the definition of flat norm: `flatNorm T = mass T + mass (boundary T)`, so convergence in flat norm implies convergence of boundaries.

## Deliverables

- [ ] Replace `axiom limit_is_calibrated` with `theorem`
- [ ] Replace `axiom flat_limit_of_cycles_is_cycle` with `theorem`
- [ ] Prove `mass_lsc_flat`, `pairing_continuous_flat`, `boundary_continuous_flat`
- [ ] `lake build Hodge.Analytic.Calibration` succeeds
- [ ] `lake build Hodge.Classical.HarveyLawson` succeeds

## Blockers

- Keep `mass_lsc` as axiom if needed (standard but technical GMT)
- The proofs are mostly about continuity/semicontinuity in flat topology

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

Prove the cohomology-level bridges that complete the proof:
1. The Harvey-Lawson output represents the original class
2. Lefschetz lifting is compatible with cycle classes

## Current Code Location

```lean
-- Hodge/Kahler/Main.lean:94
axiom harvey_lawson_fundamental_class {p : ℕ}
    (γplus : SmoothForm n X (2 * p)) (hplus : IsFormClosed γplus)
    (hγ : isConePositive γplus)
    (hl_concl : HarveyLawsonConclusion n X (2 * (n - p)))
    (T_limit : Current n X (2 * (n - p)))
    (h_represents : hl_concl.represents T_limit) :
    hl_concl.toSignedAlgebraicCycle.RepresentsClass (DeRhamCohomologyClass.ofForm γplus hplus)

-- Hodge/Kahler/Main.lean:150
axiom lefschetz_lift_signed_cycle {p p' : ℕ}
    (γ : SmoothForm n X (2 * p)) (hγ : IsFormClosed γ)
    (η : SmoothForm n X (2 * p')) (hη : IsFormClosed η)
    (Z_η : SignedAlgebraicCycle n X)
    (_hp : p > n / 2)
    (h_rep : Z_η.RepresentsClass (DeRhamCohomologyClass.ofForm η hη)) :
    ∃ Z_γ : SignedAlgebraicCycle n X, 
      Z_γ.RepresentsClass (DeRhamCohomologyClass.ofForm γ hγ)
```

## Implementation Plan

### Part 1: Harvey-Lawson Fundamental Class

```lean
theorem harvey_lawson_fundamental_class_proof {p : ℕ}
    (γplus : SmoothForm n X (2 * p)) (hplus : IsFormClosed γplus)
    (hγ : isConePositive γplus)
    (hl_concl : HarveyLawsonConclusion n X (2 * (n - p)))
    (T_limit : Current n X (2 * (n - p)))
    (h_represents : hl_concl.represents T_limit) :
    hl_concl.toSignedAlgebraicCycle.RepresentsClass (DeRhamCohomologyClass.ofForm γplus hplus) := by
  -- Step 1: T_limit represents γplus by construction
  -- T_limit = lim T_k where T_k are microstructure approximants
  -- Each T_k integrates to approximately ∫ γplus ∧ ψ
  
  -- Step 2: Harvey-Lawson theorem says T_limit = ∑ n_i [V_i]
  -- where V_i are analytic subvarieties
  
  -- Step 3: GAGA: analytic on projective ⟹ algebraic
  -- So V_i are algebraic, hence hl_concl.toSignedAlgebraicCycle is algebraic
  
  -- Step 4: Fundamental class of algebraic cycle = integration current
  -- [∑ n_i V_i] = ∑ n_i [V_i] = T_limit
  
  -- Step 5: T_limit represents γplus ⟹ fundamental class represents γplus
  
  sorry
```

**Key: the chain of representations**

```
γplus (form) 
  ↓ (microstructure construction)
T_k (integral currents)
  ↓ (flat limit)
T_limit (calibrated current)
  ↓ (Harvey-Lawson)
∑ n_i [V_i] (analytic varieties)
  ↓ (GAGA)
∑ n_i [W_i] (algebraic varieties)
  ↓ (fundamental class)
[Z] (cohomology class) = [γplus]
```

### Part 2: Lefschetz Lift

```lean
theorem lefschetz_lift_signed_cycle_proof {p p' : ℕ}
    (γ : SmoothForm n X (2 * p)) (hγ : IsFormClosed γ)
    (η : SmoothForm n X (2 * p')) (hη : IsFormClosed η)
    (Z_η : SignedAlgebraicCycle n X)
    (hp : p > n / 2)
    (h_rep : Z_η.RepresentsClass (DeRhamCohomologyClass.ofForm η hη)) :
    ∃ Z_γ : SignedAlgebraicCycle n X, 
      Z_γ.RepresentsClass (DeRhamCohomologyClass.ofForm γ hγ) := by
  -- Set p' = n - p (so p' < n/2 ≤ p)
  -- Hard Lefschetz: L^{p-p'} : H^{p',p'} ≃ H^{p,p}
  
  -- Step 1: η = L^{p-p'}(γ) by Hard Lefschetz inverse
  have h_HL := hard_lefschetz_inverse_form (n := n) (X := X) p p' hp hγ
  
  -- Step 2: At the cycle level, L corresponds to ∩ H (hyperplane intersection)
  -- If Z_η represents η, then Z_γ := "Lefschetz lift of Z_η" represents γ
  
  -- Step 3: Construct Z_γ by intersecting Z_η with (p - p') generic hyperplanes
  -- This increases codimension by (p - p')
  
  -- Step 4: Cycle class commutes with Lefschetz: [Z_γ] = L^{-(p-p')}[Z_η] = [γ]
  
  sorry
```

**Key lemma needed:**

```lean
-- Cycle classes commute with Lefschetz operator
lemma cycle_class_lefschetz_commute {p p' : ℕ} (Z : SignedAlgebraicCycle n X)
    (H : AlgebraicHyperplane n X) :
    (Z.intersect H).cycleClass (p + 1) = lefschetzL (Z.cycleClass p)
```

## Deliverables

- [ ] Replace `axiom harvey_lawson_fundamental_class` with `theorem`
- [ ] Replace `axiom lefschetz_lift_signed_cycle` with `theorem`
- [ ] Prove representation chain (microstructure → limit → HL → GAGA → fundamental class)
- [ ] Prove cycle class / Lefschetz commutation
- [ ] `lake build Hodge.Kahler.Main` succeeds

## Blockers

- **Depends on Agents C, D:** needs limit existence and limit properties
- Keep `harvey_lawson_theorem`, `serre_gaga`, `hard_lefschetz_inverse_form` as axioms (classical pillars)

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

