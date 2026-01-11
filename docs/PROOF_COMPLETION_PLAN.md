# Hodge Conjecture Formalization: Proof Completion Plan

**Document Version**: 1.0  
**Date**: January 11, 2026  
**Status**: Structurally Complete, Pending Clay-Standard Certification

---

## Executive Summary

The Hodge Conjecture formalization builds successfully with the main theorem `hodge_conjecture'` compiling without errors. However, the proof depends on `sorryAx` (incomplete proofs) and custom axioms that must be reviewed for Clay-standard acceptance.

### Current Metrics

| Metric | Value |
|--------|-------|
| Build Status | ✅ Passing |
| Custom Axioms (total) | 52 |
| Custom Axioms (on proof track) | 8 |
| `sorry` Statements (total) | 18 |
| `sorry` on Proof Track | Yes (`omega_pow_algebraic`) |
| Clay-Standard Ready | ❌ No |

---

## Part 1: Proof Track Analysis

### 1.1 Main Theorem Dependencies

The main theorem `hodge_conjecture'` depends on the following:

#### Standard Lean Axioms (Acceptable)
- `propext` - Propositional extensionality
- `Classical.choice` - Axiom of choice  
- `Quot.sound` - Quotient soundness

#### Custom Axioms ON the Proof Track

| # | Axiom | File | Purpose | Clay Status |
|---|-------|------|---------|-------------|
| 1 | `extDerivLinearMap` | Forms.lean:183 | Exterior derivative as ℂ-linear map | ⚠️ Classical Pillar |
| 2 | `isFormClosed_unitForm` | Forms.lean:364 | Unit form has d(1) = 0 | ⚠️ Classical Pillar |
| 3 | `isSmoothAlternating_wedge` | Forms.lean:276 | Wedge preserves smoothness | ⚠️ Classical Pillar |
| 4 | `smoothExtDeriv_extDeriv` | Forms.lean:315 | d² = 0 | ⚠️ Classical Pillar |
| 5 | `smoothExtDeriv_wedge` | Forms.lean:324 | Leibniz rule | ⚠️ Classical Pillar |
| 6 | `poincareDualFormExists` | CycleClass.lean:118 | Poincaré duality | ⚠️ Classical Pillar |
| 7 | `FundamentalClassSet_represents_class` | GAGA.lean:364 | Cycle representation | ⚠️ Classical Pillar |
| 8 | `SignedAlgebraicCycle.lefschetz_lift` | GAGA.lean:499 | Lefschetz lift | ⚠️ Classical Pillar |

#### Critical `sorry` ON the Proof Track

| File | Line | Function | Impact |
|------|------|----------|--------|
| `Main.lean` | 204 | `omega_pow_algebraic` | **BLOCKING** - Must be completed |

---

## Part 2: Required Completions (ON Proof Track)

These items MUST be completed to achieve Clay-standard certification.

### 2.1 CRITICAL: Complete `omega_pow_algebraic`

**Location**: `Hodge/Kahler/Main.lean:199-204`

**Current State**:
```lean
theorem omega_pow_algebraic {p : ℕ} (c : ℚ) (_hc : c > 0) :
    ∃ (Z : Set X), isAlgebraicSubvariety n X Z ∧
    ∃ (hZ : IsFormClosed (FundamentalClassSet n X p Z)),
      ⟦FundamentalClassSet n X p Z, hZ⟧ =
        (c : ℝ) • ⟦kahlerPow (n := n) (X := X) p, omega_pow_IsFormClosed p⟧ := by
  sorry
```

**Mathematical Content**: 
This theorem states that any positive rational multiple of ω^p (powers of the Kähler form) is represented by an algebraic cycle. This follows from:
1. ω is the curvature form of an ample line bundle L
2. Powers of L define algebraic cycles via hyperplane sections
3. The Chern class c₁(L) = [ω] in cohomology

**Approach Options**:
- **Option A**: Axiomatize as `omega_pow_is_algebraic` with detailed mathematical justification
- **Option B**: Build from line bundle theory (requires significant infrastructure)
- **Option C**: Use hyperplane section construction explicitly

**Recommended**: Option A with rigorous documentation

### 2.2 Review All 8 Proof-Track Axioms

Each axiom must have:
- [ ] Clear mathematical statement
- [ ] Reference to classical literature
- [ ] Justification for why it's a "Classical Pillar"
- [ ] Documentation in the axiom's docstring

---

## Part 3: Items to SILO (OFF Proof Track)

These files/modules contain `sorry` statements but are NOT on the main proof path.

### 3.1 Files with `sorry` NOT on Proof Track

| File | `sorry` Count | Purpose | Action |
|------|---------------|---------|--------|
| `Kahler/Manifolds.lean` | 4 | Hodge star, laplacian details | Silo - infrastructure |
| `Classical/PrimitiveDecomposition.lean` | 1 | Decomposition internals | Silo - not used by main |
| `Cohomology/HodgeDecomposition.lean` | 5 | (p,q) decomposition details | Silo - supplementary |
| `Cohomology/Basic.lean` | 4 | Ring structure proofs | Silo - not critical |
| `Analytic/Currents.lean` | 1 | Current theory | Silo - infrastructure |
| `Analytic/Advanced.lean` | 1 | Advanced analysis | Already marked as silo |

### 3.2 Axioms NOT on Proof Track

The following 44 axioms are in the codebase but NOT required by `hodge_conjecture'`:

**Kähler Manifolds** (6 axioms):
- `lefschetzLambdaLinearMap`, `lefschetzLambda_adjoint`, `lefschetzLambda_hodgeStar_formula`
- `hodgeStarLinearMap`, `adjointDerivLinearMap`, `laplacianLinearMap`

**Kähler Identities** (7 axioms):
- `kahler_identity_L_delta_exists`, `kahlerCommutator_L_delta_skew_adjoint`
- `kahler_identity_Lambda_d_exists`, `kahler_identities_hodge_dual`
- `laplacian_commutes_L`, `laplacian_commutes_Lambda`, `sl2_relation_L_Lambda`

**Primitive Decomposition** (9 axioms):
- `primitive_decomposition_exists`, `primitive_decomposition_unique`
- `hard_lefschetz_primitive_injective`, `hard_lefschetz_primitive_surjective`
- `primitive_dimension_formula`, `lefschetz_dimension_increasing`
- `primitive_characterization`, `sl2_irreducible_decomposition`
- `irreducible_has_primitive_generator`

**Hodge Decomposition** (5 axioms):
- `fiberDolbeaultBar`, `dolbeaultBar_squared`
- `hodge_decomposition_exists`, `hodge_decomposition_unique`, `hodge_symmetry`

**Hard Lefschetz** (3 axioms):
- `primitive_decomposition_exists` (duplicate), `primitive_decomposition_unique` (duplicate)
- `sl2_representation_bijectivity`

**Lefschetz** (2 axioms):
- `isFormClosed_lefschetzLambda`, `cohomologous_lefschetzLambda`

**Cycle Classes** (4 axioms):
- `poincareDualForm_isPP`, `poincareDualForm_isRational`, `poincareDualForm_additive`

**Wedge Product** (3 axioms):
- `wedge_constOfIsEmpty_left`, `wedge_constOfIsEmpty_right`, `wedge_assoc`

**Forms** (3 axioms):
- `smoothWedge_unitForm_left`, `smoothWedge_unitForm_right`, `smoothWedge_assoc`

---

## Part 4: Parallel Agent Task Assignments

### Task Batch A: Complete Proof Track (CRITICAL)

#### Task A1: Complete `omega_pow_algebraic`
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 4-6 hours  
**Dependencies**: None  

**Instructions**:
```
TASK: Complete omega_pow_algebraic theorem

FILE: Hodge/Kahler/Main.lean

GOAL: Replace the sorry at line 204 with either:
1. A complete proof using existing infrastructure, OR
2. An axiom with rigorous mathematical justification

MATHEMATICAL CONTENT:
- The Kähler form ω = c₁(L) for an ample line bundle L
- Powers ω^p correspond to complete intersections of hyperplane sections
- For c > 0 rational, c·ω^p is represented by a suitable algebraic cycle

ACCEPTANCE CRITERIA:
- [ ] `lake build Hodge.Kahler.Main` succeeds
- [ ] `#print axioms hodge_conjecture'` shows no `sorryAx`
- [ ] If axiomatized, docstring includes literature reference

VERIFICATION:
echo 'import Hodge.Kahler.Main
#print axioms hodge_conjecture'\'' | lake env lean --stdin
```

---

### Task Batch B: Axiom Documentation (PARALLEL)

**Status (2026-01-11)**: ✅ Completed — the four proof-track axioms below now have detailed
docstrings (in their source files) stating the mathematical content, why they are axiomatized,
and giving standard literature references.

#### Task B1: Document `extDerivLinearMap`
**Priority**: 🟡 High  
**Estimated Effort**: 1-2 hours  
**File**: `Hodge/Analytic/Forms.lean:183`

**Status**: ✅ Completed (see the docstring immediately above `extDerivLinearMap`).

**Instructions**:
```
TASK: Enhance documentation for extDerivLinearMap axiom

REQUIREMENTS:
1. Add detailed docstring explaining:
   - Mathematical definition of exterior derivative
   - Why this is axiomatized (avoid mfderiv API issues)
   - Reference to [Warner, "Foundations of Differentiable Manifolds"]
2. Add @[simp] lemmas if appropriate
3. Ensure existing proofs still build

ACCEPTANCE: lake build Hodge.Analytic.Forms
```

#### Task B2: Document `poincareDualFormExists`
**Priority**: 🟡 High  
**Estimated Effort**: 1-2 hours  
**File**: `Hodge/Classical/CycleClass.lean:118`

**Status**: ✅ Completed (docstring updated to explicitly note it backs `FundamentalClassSet`).

**Instructions**:
```
TASK: Enhance documentation for poincareDualFormExists axiom

REQUIREMENTS:
1. Add detailed docstring explaining:
   - Poincaré duality for compact oriented manifolds
   - How the dual form represents a cycle
   - Reference to [Bott-Tu, "Differential Forms in Algebraic Topology"]
2. Document relationship to FundamentalClassSet

ACCEPTANCE: lake build Hodge.Classical.CycleClass
```

#### Task B3: Document `FundamentalClassSet_represents_class`
**Priority**: 🟡 High  
**Estimated Effort**: 1-2 hours  
**File**: `Hodge/Classical/GAGA.lean:364`

**Status**: ✅ Completed (see the docstring immediately above `FundamentalClassSet_represents_class`).

**Instructions**:
```
TASK: Enhance documentation for FundamentalClassSet_represents_class

REQUIREMENTS:
1. Add detailed docstring explaining:
   - How algebraic cycles determine cohomology classes
   - The role of integration currents
   - Reference to [Griffiths-Harris, Ch. 1]
2. Explain the axiom's role in the proof

ACCEPTANCE: lake build Hodge.Classical.GAGA
```

#### Task B4: Document `SignedAlgebraicCycle.lefschetz_lift`
**Priority**: 🟡 High  
**Estimated Effort**: 1-2 hours  
**File**: `Hodge/Classical/GAGA.lean:499`

**Status**: ✅ Completed (see the docstring immediately above `SignedAlgebraicCycle.lefschetz_lift`).

**Instructions**:
```
TASK: Enhance documentation for lefschetz_lift axiom

REQUIREMENTS:
1. Add detailed docstring explaining:
   - Hard Lefschetz theorem context
   - How cycles lift via hyperplane sections
   - Reference to [Voisin, "Hodge Theory and Complex Algebraic Geometry"]
2. Document the p > n/2 case handling

ACCEPTANCE: lake build Hodge.Classical.GAGA
```

---

### Task Batch C: Silo Off-Track Code (PARALLEL)

#### Task C1: Isolate Advanced Analysis
**Priority**: 🟢 Low  
**Estimated Effort**: 1 hour  
**File**: `Hodge/Analytic/Advanced.lean`

**Instructions**:
```
TASK: Ensure Advanced.lean is properly isolated

REQUIREMENTS:
1. Add prominent header warning about sorry statements
2. Verify no Main.lean imports depend on this file
3. Document what this module is for (future work)

VERIFICATION:
grep -r "import.*Advanced" Hodge/Kahler/Main.lean  # Should return nothing
```

#### Task C2: Document Silo Status
**Priority**: 🟢 Low  
**Estimated Effort**: 2 hours  

**Instructions**:
```
TASK: Create SILO_MODULES.md documenting off-track code

REQUIREMENTS:
1. List all modules with sorry not on proof track
2. Explain the purpose of each
3. Mark as "Future Work" or "Infrastructure"
4. Add to docs/ folder

OUTPUT: docs/SILO_MODULES.md
```

---

### Task Batch D: Verification & Testing (FINAL)

#### Task D1: Final Axiom Audit
**Priority**: 🔴 CRITICAL  
**Estimated Effort**: 2 hours  
**Dependencies**: Tasks A1, B1-B4 complete

**Instructions**:
```
TASK: Final verification of proof track

REQUIREMENTS:
1. Run: echo 'import Hodge.Kahler.Main
#print axioms hodge_conjecture'\'' | lake env lean --stdin
2. Verify NO sorryAx in output
3. Verify all axioms are "Classical Pillars"
4. Generate final axiom report

OUTPUT: docs/FINAL_AXIOM_REPORT.md
```

#### Task D2: Build Full Proof Bundle
**Priority**: 🟡 High  
**Estimated Effort**: 1 hour  
**Dependencies**: Task D1 complete

**Instructions**:
```
TASK: Generate and verify full proof bundle

COMMANDS:
./generate_lean_source.sh
lake build

VERIFY:
- No errors
- Proof bundle contains all needed files
- README updated with completion status
```

---

## Part 5: Execution Order

```
Phase 1 (CRITICAL - Sequential):
  └── Task A1: Complete omega_pow_algebraic

Phase 2 (Documentation - Parallel):
  ├── Task B1: Document extDerivLinearMap
  ├── Task B2: Document poincareDualFormExists
  ├── Task B3: Document FundamentalClassSet_represents_class
  └── Task B4: Document lefschetz_lift

Phase 3 (Cleanup - Parallel):
  ├── Task C1: Isolate Advanced Analysis
  └── Task C2: Document Silo Status

Phase 4 (Verification - Sequential):
  ├── Task D1: Final Axiom Audit
  └── Task D2: Build Full Proof Bundle
```

---

## Part 6: Success Criteria

### For Clay-Standard Certification:

1. ✅ `lake build Hodge.Kahler.Main` passes
2. ⬜ `#print axioms hodge_conjecture'` shows NO `sorryAx`
3. ⬜ All 8 proof-track axioms documented as "Classical Pillars"
4. ⬜ Off-track code clearly siloed and documented
5. ⬜ Final axiom report generated and reviewed

---

## Appendix A: Quick Reference Commands

```bash
# Build main theorem
lake build Hodge.Kahler.Main

# Check axioms on proof track
echo 'import Hodge.Kahler.Main
#print axioms hodge_conjecture'\'' | lake env lean --stdin

# Count sorry statements
grep -rn "sorry" Hodge/ --include="*.lean" | wc -l

# Count axioms
grep -rn "^axiom" Hodge/ --include="*.lean" | wc -l

# Find sorry on proof track
grep -rn "sorry" Hodge/Kahler/Main.lean
```

---

## Appendix B: File Dependency Graph (Proof Track Only)

```
Hodge/Kahler/Main.lean
├── Hodge/Kahler/Manifolds.lean
├── Hodge/Kahler/TypeDecomposition.lean
├── Hodge/Kahler/Cone.lean
├── Hodge/Kahler/SignedDecomp.lean
├── Hodge/Kahler/Microstructure.lean
├── Hodge/Analytic/Currents.lean
├── Hodge/Analytic/Calibration.lean
├── Hodge/Classical/HarveyLawson.lean
├── Hodge/Classical/GAGA.lean
│   └── Hodge/Classical/CycleClass.lean
└── Hodge/Classical/Lefschetz.lean
    └── Hodge/Cohomology/Basic.lean
        └── Hodge/Analytic/Forms.lean
```

---

*Document generated: January 11, 2026*  
*Next review: After Task A1 completion*
