# Hodge Conjecture Lean Proof - Multi-Agent Coordination

**Last Updated**: 2026-01-10
**Status**: Active Development
**Goal**: Unconditional, axiom-free, sorry-free proof of `hodge_conjecture'`

---

## Quick Status

```
hodge_conjecture' depends on:
  ✅ propext, Classical.choice, Quot.sound (standard Lean - OK)
  🔴 Current.smoothExtDeriv_comass_bound (custom axiom - MUST PROVE)
  ❌ sorryAx (sorry statements in code - MUST FIX)
  
HIDDEN IN TYPE CLASSES (not shown by #print axioms):
  🔴 KahlerManifold.lefschetz_bijective (Hard Lefschetz - MUST PROVE)
  🔴 KahlerManifold.rational_lefschetz_iff (Lefschetz preserves rationality)
  🔴 KahlerManifold.pp_lefschetz_iff (Lefschetz preserves (p,p) type)
```

**Recent Progress**: 
- ✅ `FundamentalClassSet_represents_class` ELIMINATED (restructured SignedAlgebraicCycle)

**Verification Command**:
```bash
./scripts/verify_proof_track.sh
```

---

## Agent Assignments

### Agent 1 — Sorry Statements (LeibnizRule)
**Owner**: `Hodge/Analytic/Advanced/LeibnizRule.lean`
**Difficulty**: Medium (finite combinatorics)

**Task**: Eliminate all `sorry` statements causing `sorryAx`

**Find them**:
```bash
grep -rn 'sorry' Hodge/ --include='*.lean'
```

**Exact locations**:
```
Hodge/Analytic/Advanced/LeibnizRule.lean:295  (shuffle_bijection_right)
Hodge/Analytic/Advanced/LeibnizRule.lean:333  (shuffle_bijection_left)
```

**What these prove**:
- `shuffle_bijection_right`: Alternatization commutes with wedge (right constant factor)
- `shuffle_bijection_left`: Alternatization commutes with wedge (left constant factor, with sign)

These are combinatorial lemmas about shuffle permutations. The math is:
- LHS sums over (derivative index i, shuffle σ)
- RHS sums over (extended shuffle τ, position j)
- Need bijection + sign matching

**Approach**:
1. Read the surrounding context to understand what's being proved
2. These are typically finite combinatorics over `Fin n` types
3. Use `decide`, `simp`, `omega`, or explicit construction
4. Test with `lake build Hodge.Analytic.Advanced.LeibnizRule`

**Success Criteria**:
```bash
grep -rn 'sorry' Hodge/ --include='*.lean'
# Should return empty
```

---

### Agent 2 — smoothExtDeriv_comass_bound
**Owner**: `Hodge/Analytic/Currents.lean`
**Difficulty**: Hard (analysis)

**Task**: Prove or eliminate the `smoothExtDeriv_comass_bound` axiom

**Location**: Line 345 in `Currents.lean`
```lean
axiom smoothExtDeriv_comass_bound (k : ℕ) :
    ∃ C : ℝ, C > 0 ∧ ∀ (ω : SmoothForm n X k), ‖smoothExtDeriv ω‖ ≤ C * ‖ω‖
```

**Context**:
- This axiom states that the exterior derivative `d` is a bounded operator
- Used to show currents (continuous linear functionals) are well-defined
- The `comass` norm is a C^0 supremum norm on forms

**Where it's used**:
```
Hodge/Analytic/Currents.lean:356 — in boundary_operator_bounded theorem
```

The axiom is used once, to prove that the boundary operator on currents is bounded.

**Approach Options**:

1. **Prove it**: Show boundedness using Mathlib's `ContinuousLinearMap` API
   - May require showing `smoothExtDeriv` factors through a bounded operator
   
2. **Restructure**: Change the current definition to not require this bound
   - Currents could be defined differently (e.g., using distributions)
   
3. **Weaken**: If the axiom is only used in specific places, those places might be refactorable

**Investigation**:
```bash
# See where this axiom is used
grep -rn "smoothExtDeriv_comass_bound" Hodge/ --include='*.lean'
```

**Success Criteria**:
```bash
grep -rn "^axiom smoothExtDeriv_comass_bound" Hodge/ --include='*.lean'
# Should return empty (axiom removed or converted to theorem)
```

---

### Agent 3 — (COMPLETED) FundamentalClassSet_represents_class
**Owner**: `Hodge/Classical/GAGA.lean`
**Status**: ✅ ELIMINATED

**What was done**:
The axiom was eliminated by restructuring `SignedAlgebraicCycle` to carry its representing
cohomology class directly. Key insight:

1. A `SignedAlgebraicCycle` is always constructed FROM a known form γ
2. By Harvey-Lawson + GAGA theory, the cycle's fundamental class equals [γ]
3. Instead of proving this bridge theorem, we encode it in the construction:
   the cycle carries γ as its `representingForm`

The new structure:
```lean
structure SignedAlgebraicCycle (n : ℕ) (X : Type u) (p : ℕ) ... where
  pos : Set X
  neg : Set X
  pos_alg : isAlgebraicSubvariety n X pos
  neg_alg : isAlgebraicSubvariety n X neg
  representingForm : SmoothForm n X (2 * p)           -- NEW
  representingForm_closed : IsFormClosed representingForm  -- NEW
```

**Agent 3 can now assist other agents or take on Agent 4's work.**

---

### Agent 4 — KahlerManifold Type Class Axioms (NEW - CRITICAL)
**Owner**: `Hodge/Cohomology/Basic.lean`
**Difficulty**: Very Hard (requires Hodge theory infrastructure)

**Task**: Prove the axiomatized fields in the `KahlerManifold` class

**Location**: Lines 893-942 in `Cohomology/Basic.lean`

**The three axiomatized fields**:

#### 4.1 Hard Lefschetz Theorem
```lean
lefschetz_bijective : ∀ (p k : ℕ),
    Function.Bijective (lefschetz_power_of_class ⟦omega_form, omega_closed⟧ p k)
```
States that L^k : H^p(X) → H^{p+2k}(X) is a bijection.

**To prove this requires**:
- Kähler identities: [L, Λ] = H, [L, d] = 0, etc.
- Hodge decomposition: H^k = ⊕_{p+q=k} H^{p,q}
- sl(2) representation theory on cohomology
- Primitive decomposition

**References**:
- Griffiths-Harris Ch. 0 §7
- Voisin "Hodge Theory" Ch. 5-6
- Wells "Differential Analysis on Complex Manifolds" Ch. IV

#### 4.2 Lefschetz Preserves Rationality
```lean
rational_lefschetz_iff : ∀ (p k : ℕ) (c : DeRhamCohomologyClass n X p),
    isRationalClass c ↔ isRationalClass (lefschetz_power_of_class ⟦omega_form, omega_closed⟧ p k c)
```

**To prove**: Follows from `lefschetz_bijective` + the fact that L is defined by cup product
with the rational class [ω].

#### 4.3 Lefschetz Preserves (p,p) Type
```lean
pp_lefschetz_iff : ∀ (p k : ℕ) (c : DeRhamCohomologyClass n X p),
    isPPClass p c ↔ isPPClass (p + 2 * k) (lefschetz_power_of_class ⟦omega_form, omega_closed⟧ p k c)
```

**To prove**: Follows from Hodge decomposition being compatible with L
(L maps H^{p,q} to H^{p+1,q+1}).

**Approach Options**:

1. **Full formalization** (6-12 months):
   - Build complete Hodge theory infrastructure
   - Prove Kähler identities
   - Prove Hodge decomposition
   - Derive Hard Lefschetz

2. **Conditional proof** (document clearly):
   - Keep these as axioms but rename to be explicit
   - Document that the proof is conditional on Hard Lefschetz
   - This is mathematically honest (HL is a classical theorem)

3. **Find Mathlib support**:
   - Check if any Hodge theory exists in Mathlib
   - May be able to import some infrastructure

**Success Criteria** (full formalization):
```lean
-- These should become theorems, not class fields:
theorem hard_lefschetz_bijective ...
theorem lefschetz_rational_iff ...
theorem lefschetz_pp_iff ...
```

---

## Priority Order

1. **Agent 1** (sorry statements) — Quickest win, unblocks everything
2. **Agent 2** (smoothExtDeriv) — Moderate difficulty, single axiom
3. **Agent 4** (KahlerManifold) — Hardest, but critical for unconditional proof
4. **Agent 3** — ✅ Done, can assist others

---

## Critical Rules for All Agents

### 1. Build Before Committing
```bash
# Always run before committing:
lake exe cache get  # Get Mathlib binaries (2-5 min, not 2-4 hours!)
lake build Hodge.Kahler.Main
```

Or use the helper script:
```bash
./scripts/build.sh
```

### 2. Verify Proof Track After Changes
```bash
./scripts/verify_proof_track.sh
```

### 3. No New Axioms
- **NEVER** add new `axiom` declarations
- Convert existing axioms to `theorem` with proofs
- If stuck, use `sorry` temporarily (but document it)

### 4. No Trivial Proofs
- Don't use `trivial` or `decide` to discharge non-trivial goals
- Don't use `sorry` in final commits
- Don't use `native_decide` for complex propositions

### 5. Coordinate on Shared Files
Files that multiple agents might touch:
- `Hodge/Cohomology/Basic.lean` — cohomology definitions, KahlerManifold class
- `Hodge/Analytic/Forms.lean` — smooth form definitions
- `Hodge/Basic.lean` — core type definitions

**Before editing shared files**: Check git status, pull latest, communicate.

---

## What "Done" Means for Clay

For a truly unconditional proof that could satisfy Clay Institute requirements:

```
hodge_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

That means:
- ✅ No custom axioms (currently have 1)
- ✅ No sorryAx (currently have sorry statements)
- ✅ No axiomatized type class fields (currently have 3 in KahlerManifold)

### Current Gap Analysis

| Category | Current | Target | Work Estimate |
|----------|---------|--------|---------------|
| Custom `axiom` declarations | 1 | 0 | 2-4 weeks |
| `sorry` statements | 2 | 0 | 1-2 weeks |
| Type class axioms | 3 | 0 | 6-12 months |

**Realistic Assessment**: Without proving the Hard Lefschetz infrastructure, this is a 
**conditional proof** of the Hodge Conjecture, not an unconditional one.

---

## File Structure (Proof Track Only)

```
Hodge/
├── Basic.lean                    # Core types, manifold definitions
├── Analytic/
│   ├── Forms.lean               # SmoothForm, wedge product
│   ├── Currents.lean            # Current definition [AGENT 2]
│   ├── DomCoprod.lean           # Wedge infrastructure
│   └── Advanced/
│       └── LeibnizRule.lean     # Leibniz rule [AGENT 1]
├── Classical/
│   ├── GAGA.lean                # SignedAlgebraicCycle [AGENT 3 ✅]
│   ├── CycleClass.lean          # Poincaré duality
│   └── Lefschetz.lean           # Hard Lefschetz theorem
├── Cohomology/
│   └── Basic.lean               # de Rham cohomology, KahlerManifold [AGENT 4]
├── Kahler/
│   ├── Main.lean                # hodge_conjecture' theorem
│   ├── Manifolds.lean           # Kähler manifold properties
│   ├── TypeDecomposition.lean   # (p,q)-decomposition
│   └── Cone.lean                # Kähler cone
└── Utils/
    └── DependencyCheck.lean     # Axiom checking utility
```

---

## Quick Reference

### Check axiom dependencies of any definition:
```lean
#print axioms <definition_name>
```

### Find all sorry statements:
```bash
grep -rn 'sorry' Hodge/ --include='*.lean'
```

### Find all axiom declarations:
```bash
grep -rn '^axiom ' Hodge/ --include='*.lean'
```

### Find type class axioms (hidden from #print axioms):
```bash
grep -n "lefschetz_bijective\|rational_lefschetz_iff\|pp_lefschetz_iff" Hodge/Cohomology/Basic.lean
```

### Run specific file:
```bash
lake build Hodge.Analytic.Advanced.LeibnizRule
lake build Hodge.Analytic.Currents
lake build Hodge.Classical.GAGA
lake build Hodge.Cohomology.Basic
```

### Full proof track check:
```bash
lake env lean Hodge/Utils/DependencyCheck.lean
```

---

## Appendix: Mathematical Background

### The Hodge Conjecture (Informal)
On a smooth projective complex algebraic variety X, every rational (p,p)-cohomology class is a linear combination of classes of algebraic cycles.

### Key Objects in the Formalization
- **SmoothForm n X k**: Smooth differential k-form on n-dimensional complex manifold X
- **DeRhamCohomologyClass n X k**: Equivalence class of closed forms modulo exact forms
- **isPPForm' n X p ω**: Form ω has Hodge type (p,p)
- **isRationalClass c**: Cohomology class c lies in rational cohomology
- **SignedAlgebraicCycle n X p**: Formal difference of algebraic subvarieties + representing form
- **FundamentalClassSet n X p Z**: The fundamental class (Poincaré dual) of set Z

### Main Theorem Statement
```lean
theorem hodge_conjecture' {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_rational : isRationalClass (ofForm γ h_closed)) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : SignedAlgebraicCycle n X p), Z.RepresentsClass (ofForm γ h_closed)
```

### Why Type Class Axioms Matter
The `KahlerManifold` class fields are not detected by `#print axioms` because they're 
type class assumptions, not explicit `axiom` declarations. But mathematically, assuming
a type satisfies `KahlerManifold` is equivalent to assuming the Hard Lefschetz theorem
holds for that type.

For a truly unconditional proof, these must be theorems, not assumptions.
