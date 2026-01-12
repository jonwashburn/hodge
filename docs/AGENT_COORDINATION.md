# Hodge Conjecture Lean Proof - Multi-Agent Coordination

**Last Updated**: 2026-01-10
**Status**: Active Development
**Goal**: Unconditional, axiom-free, sorry-free proof of `hodge_conjecture'`

---

## Quick Status

```
hodge_conjecture' depends on:
  ✅ propext, Classical.choice, Quot.sound (standard Lean - OK)
  🔴 FundamentalClassSet_represents_class (custom axiom - MUST PROVE)
  🔴 Current.smoothExtDeriv_comass_bound (custom axiom - MUST PROVE)  
  ❌ sorryAx (sorry statements in code - MUST FIX)
```

**Verification Command**:
```bash
./scripts/verify_proof_track.sh
```

---

## Agent Assignments

### Agent 1 — Sorry Statements (LeibnizRule)
**Owner**: `Hodge/Analytic/Advanced/LeibnizRule.lean`

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

**Approach Options**:

1. **Prove it**: Show boundedness using Mathlib's `ContinuousLinearMap` API
   - May require showing `smoothExtDeriv` factors through a bounded operator
   
2. **Restructure**: Change the current definition to not require this bound
   - Currents could be defined differently (e.g., using distributions)
   
3. **Weaken**: If the axiom is only used in specific places, those places might be refactorable

**Where it's used**:
```
Hodge/Analytic/Currents.lean:356 — in boundary_operator_bounded theorem
```

The axiom is used once, to prove that the boundary operator on currents is bounded.

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

### Agent 3 — FundamentalClassSet_represents_class
**Owner**: `Hodge/Classical/GAGA.lean`

**Task**: Prove or eliminate the `FundamentalClassSet_represents_class` axiom

**Location**: Line 376 in `GAGA.lean`
```lean
axiom FundamentalClassSet_represents_class (p : ℕ) (Z : Set X) [Nonempty X]
    (γ : SmoothForm n X (2 * p)) (hγ : IsFormClosed γ)
    (h_alg : isAlgebraicSubvariety n X Z) (h_rational : isRationalClass (ofForm γ hγ)) :
    ⟦FundamentalClassSet n X p Z, FundamentalClassSet_isClosed p Z h_alg⟧ = ofForm γ hγ
```

**Context**:
- This is the deep GAGA (Géométrie Algébrique et Géométrie Analytique) principle
- States: if Z is an algebraic subvariety and γ is a rational closed form, then
  the fundamental class of Z equals the cohomology class of γ
- This connects algebraic geometry to differential geometry

**Approach Options**:

1. **Prove from existing structure**: 
   - Check if `FundamentalClassSet` definition already implies this
   - Look at `fundamentalClassImpl` and `poincareDualForm` definitions
   
2. **Add required infrastructure**:
   - May need integration currents
   - May need Stokes' theorem
   
3. **Restructure the proof**:
   - The main theorem `hodge_conjecture'` might be provable via different route

**Where it's used**:
```
Hodge/Kahler/Main.lean:125 — in cone_positive_represents theorem
```

This is the key step that produces algebraic cycle representatives from cone-positive classes.

**Investigation**:
```bash
# See how FundamentalClassSet is defined
grep -rn "def FundamentalClassSet" Hodge/ --include='*.lean'
grep -rn "FundamentalClassSet_impl" Hodge/ --include='*.lean'
```

**Success Criteria**:
```bash
grep -rn "^axiom FundamentalClassSet_represents_class" Hodge/ --include='*.lean'
# Should return empty (axiom removed or converted to theorem)
```

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

Expected output for success:
```
Custom axioms to prove: 0
Sorry statements: NOT FOUND ✅
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
- `Hodge/Cohomology/Basic.lean` — cohomology definitions
- `Hodge/Analytic/Forms.lean` — smooth form definitions
- `Hodge/Basic.lean` — core type definitions

**Before editing shared files**: Check git status, pull latest, communicate.

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
│   ├── GAGA.lean                # Fundamental class [AGENT 3]
│   ├── CycleClass.lean          # Poincaré duality
│   └── Lefschetz.lean           # Hard Lefschetz theorem
├── Cohomology/
│   └── Basic.lean               # de Rham cohomology
├── Kahler/
│   ├── Main.lean                # hodge_conjecture' theorem
│   ├── Manifolds.lean           # Kähler manifold properties
│   ├── TypeDecomposition.lean   # (p,q)-decomposition
│   └── Cone.lean                # Kähler cone
└── Utils/
    └── DependencyCheck.lean     # Axiom checking utility
```

---

## Communication Protocol

### When You Complete a Task
1. Run `./scripts/verify_proof_track.sh`
2. Commit with descriptive message
3. Update this document's "Quick Status" section
4. Note any blockers or dependencies on other agents

### When You're Blocked
Document:
- What you tried
- What error/issue you hit
- What you need from another agent

### When You Modify Shared Infrastructure
- Note the change in your commit message
- Consider if it affects other agents' work

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

### Run specific file:
```bash
lake build Hodge.Analytic.Advanced.LeibnizRule
lake build Hodge.Analytic.Currents
lake build Hodge.Classical.GAGA
```

### Full proof track check:
```bash
lake env lean Hodge/Utils/DependencyCheck.lean
```

---

## Success Definition

The proof is complete when:

```bash
$ ./scripts/verify_proof_track.sh

'hodge_conjecture'' depends on axioms: [propext, Classical.choice, Quot.sound]

SUMMARY
═══════════════════════════════════════════════════════
   Standard Lean axioms: 3 (always present, acceptable)
   Custom axioms to prove: 0
   Sorry statements: NOT FOUND ✅

✅ SUCCESS: Proof is complete! No custom axioms or sorry.
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
- **SignedAlgebraicCycle n X**: Formal difference of algebraic subvarieties
- **FundamentalClassSet n X p Z**: The fundamental class (Poincaré dual) of set Z

### Main Theorem Statement
```lean
theorem hodge_conjecture' {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_rational : isRationalClass (ofForm γ h_closed)) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : SignedAlgebraicCycle n X), Z.RepresentsClass (ofForm γ h_closed)
```
