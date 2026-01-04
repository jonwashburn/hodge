# Implementation Plan: Non-Vacuous Hodge Conjecture Formalization

## Executive Summary

The current Lean formalization has correct **proof architecture** but **vacuous mathematical content**. The core operations (wedge product, exterior derivative, fundamental class, inner product) are all defined as zero, which means:

- Every cohomology class equals 0
- The "proof" only shows: "If [γ] = 0, then [γ] is algebraic" (trivially true)

This document outlines a phased plan to replace vacuous definitions with real mathematical content.

---

## Implementation Status (Updated)

### Completed Changes

1. **FundamentalClassSet is now opaque** (GAGA.lean)
   - Changed from `def ... := 0` to `opaque` with explicit axioms
   - Added 5 new infrastructure axioms for its properties:
     - `FundamentalClassSet_isClosed`
     - `FundamentalClassSet_empty`
     - `FundamentalClassSet_is_p_p`
     - `FundamentalClassSet_additive`
     - `FundamentalClassSet_rational`

2. **lefschetz_lift_signed_cycle is now an axiom** (Main.lean)
   - Was a "theorem" with vacuous proof (relied on all cycle classes = 0)
   - Now properly axiomatized as infrastructure for Lefschetz lifting

3. **Build errors fixed** in:
   - `Grassmannian.lean` - type coercions
   - `Bergman.lean` - transition holomorphicity (1 sorry remains)
   - `Cone.lean` - calibrated cone definitions
   - `Microstructure.lean` - arithmetic and Current lemmas

### Current Axiom Count: 15

| Category | Axioms | Notes |
|----------|--------|-------|
| 8 Classical Pillars | 8 | Fed-Flem, Mass LSC, GAGA, Spine, Harvey-Lawson, Hard Lefschetz (2), ω^p algebraic |
| Fundamental Class Infrastructure | 5 | Properties of the opaque FundamentalClassSet |
| Lefschetz Lift | 1 | Cycle construction via hyperplane intersection |
| Cone Interior | 1 | exists_uniform_interior_radius |

### Remaining Sorrys: 1
- `Bergman.lean:190` - Bundle transition holomorphicity (infrastructure placeholder)

---

## Current State (Vacuous Definitions)

| Definition | File:Line | Current Value | Impact |
|------------|-----------|---------------|--------|
| `smoothWedge` | Forms.lean:500 | `0` | Kähler powers trivial |
| `extDerivLinearMap` | Forms.lean:448 | `0` | All forms closed, none exact |
| `FundamentalClassSet` | GAGA.lean:217 | `0` | All cycle classes = 0 |
| `pointwiseInner` | Norms.lean:301 | `0` | L² theory vacuous |
| `L2Inner` | Norms.lean:321 | `0` | No energy functional |

---

## Phase 1: Real Wedge Product (HIGH PRIORITY)

### Why First
The wedge product is foundational. Without it:
- `ω^p` (Kähler powers) are all 0
- Cup product on cohomology is trivial
- Lefschetz operator `L(η) = ω ∧ η` is 0

### Implementation Strategy

Mathlib provides `AlternatingMap.domCoprod` for the wedge product of alternating maps. We need to:

1. Define wedge product using `AlternatingMap.domCoprod`
2. Prove smoothness (the composition of smooth forms is smooth)
3. Prove algebraic properties (associativity, graded commutativity)

### Code Location
- `Hodge/Analytic/Forms.lean` lines 500-548

### Implementation

```lean
-- Replace the zero definition with a real wedge product
def smoothWedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) : 
    SmoothForm n X (k + l) :=
  { as_alternating := fun x => 
      AlternatingMap.domCoprod (ω.as_alternating x) (η.as_alternating x),
    is_smooth := smoothWedge_smooth ω η }
```

### Dependencies
- Mathlib.LinearAlgebra.Alternating.DomCoprod (already imported)
- Need to prove `smoothWedge_smooth`: continuity of the wedge

### Estimated Effort: 4-6 hours

---

## Phase 2: Non-Trivial Fundamental Class (CRITICAL)

### Why Critical
The fundamental class map is what connects algebraic cycles to cohomology. With `FundamentalClassSet = 0`:
- Every cycle represents the zero class
- The theorem is vacuous

### Implementation Strategy

The fundamental class of a subvariety Z ⊂ X is a closed (p,p)-form representing the Poincaré dual. There are two approaches:

#### Option A: Axiomatic (Honest about what we're assuming)

Keep `FundamentalClassSet` as an axiom with proper properties:

```lean
-- Declare as opaque with axioms for its properties
opaque FundamentalClassSet (n : ℕ) (X : Type u) ... (p : ℕ) (Z : Set X) : 
    SmoothForm n X (2 * p)

axiom FundamentalClassSet_nontrivial : 
    ∃ (Z : Set X), FundamentalClassSet n X 1 Z ≠ 0

axiom FundamentalClassSet_additive (p : ℕ) (Z₁ Z₂ : Set X) :
    FundamentalClassSet n X p (Z₁ ∪ Z₂) = 
      FundamentalClassSet n X p Z₁ + FundamentalClassSet n X p Z₂ - 
      FundamentalClassSet n X p (Z₁ ∩ Z₂)

axiom FundamentalClassSet_functorial (f : X → Y) (Z : Set X) :
    -- Pushforward property
```

#### Option B: Constructive (Requires substantial infrastructure)

Define via the current of integration:

```lean
def FundamentalClassSet (p : ℕ) (Z : Set X) : SmoothForm n X (2 * p) :=
  -- The smooth form η such that for all test forms α:
  -- ∫_X η ∧ α = ∫_Z α|_Z
  -- This requires:
  -- 1. Integration theory on manifolds
  -- 2. Restriction of forms to submanifolds
  -- 3. Regularity theory (smoothing of currents)
```

### Recommended Approach

Start with **Option A** to make the theorem non-vacuous immediately, then work toward **Option B** as infrastructure becomes available.

### Code Location
- `Hodge/Classical/GAGA.lean` lines 206-261

### Estimated Effort: 2-3 hours (Option A), 40+ hours (Option B)

---

## Phase 3: Real Exterior Derivative

### Why Important
With `d = 0`:
- Every form is closed
- De Rham cohomology degenerates to "all closed forms"
- The exactness quotient is trivial

### Implementation Strategy

The exterior derivative requires coordinate-based computation:

```lean
def extDerivLinearMap (n : ℕ) (X : Type u) ... (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (k + 1) :=
  { toFun := fun ω => 
      { as_alternating := fun x => 
          -- d(ω)(v₀,...,vₖ) = Σᵢ (-1)^i ∂ᵢ(ω(v₀,...,v̂ᵢ,...,vₖ)) + ...
          extDerivAt (ω.as_alternating) x,
        is_smooth := ... },
    map_add' := ...,
    map_smul' := ... }
```

### Dependencies
- Mathlib differential calculus on manifolds
- Chart-based coordinate formulas

### Alternative: Keep as Axiom
If full implementation is too complex, axiomatize with properties:

```lean
axiom extDeriv_extDeriv_eq_zero : d (d ω) = 0  -- Already satisfied by d = 0
axiom extDeriv_wedge_leibniz : d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη
```

### Estimated Effort: 8-12 hours (full), 2 hours (axiomatic)

---

## Phase 4: Real Inner Product

### Why Important
Without inner product:
- L² Hodge theory is vacuous
- Energy minimization has no content
- Calibration theory degenerates

### Implementation Strategy

```lean
def pointwiseInner {k : ℕ} (α β : SmoothForm n X k) (x : X) : ℝ :=
  -- ⟨α, β⟩_x = Σ_{I} α_I(x) * conj(β_I(x)) * g^{I,I}(x)
  -- where g is the Kähler metric
  inner (α.as_alternating x) (β.as_alternating x)

def L2Inner {k : ℕ} (α β : SmoothForm n X k) : ℝ :=
  ∫ x in X, pointwiseInner α β x ∂μ
```

### Dependencies
- Inner product on alternating maps (from Kähler metric)
- Integration on manifolds (MeasureTheory)
- Volume form from Kähler structure

### Estimated Effort: 6-10 hours

---

## Prioritized Execution Order

### Week 1: Make Theorem Non-Vacuous

1. **Day 1-2**: Implement axiomatic `FundamentalClassSet` (Option A)
   - Change from `= 0` to `opaque` with axioms
   - Add axiom for nontriviality
   - Update dependent proofs

2. **Day 3-4**: Implement real `smoothWedge`
   - Use `AlternatingMap.domCoprod`
   - Prove basic properties
   - Update `kahlerPow` to use real wedge

3. **Day 5**: Update documentation and test build

### Week 2: Core Operations

4. **Day 1-3**: Implement real exterior derivative (axiomatic approach)
   - Define properties as axioms
   - Ensure d² = 0 is a theorem (not trivial)

5. **Day 4-5**: Implement inner product structure
   - Pointwise inner product
   - L² integration

### Week 3: Integration and Testing

6. Verify all proofs still compile
7. Update `PROOF_COMPLETION_PLAN_8_PILLARS.md`
8. Document remaining axioms
9. Create test suite for new definitions

---

## Success Criteria

### Minimal Success (Week 1)
- `FundamentalClassSet` is not identically zero
- `smoothWedge` is a real wedge product
- The theorem has mathematical content

### Full Success (Week 3)
- All core operations have real implementations
- Axiom count is reduced to the 8 classical pillars
- Build passes with no new sorrys

---

## Risk Assessment

| Risk | Probability | Mitigation |
|------|------------|------------|
| Mathlib API doesn't support needed operations | Medium | Use axiomatic approach as fallback |
| Type-level dimension issues with wedge | High | Careful use of `Nat.add_comm` coercions |
| Integration on manifolds not available | High | Axiomatize L² operations |
| Proof complexity explosion | Medium | Incremental commits, test after each change |

---

## Getting Started

```bash
# Create a branch for this work
git checkout -b feature/non-vacuous-definitions

# Start with the most impactful change: fundamental class
# Edit Hodge/Classical/GAGA.lean
```

---

## Related Documents

- `PROOF_COMPLETION_PLAN_8_PILLARS.md` - Overall completion plan
- `docs/plans/REFACTORING_PLAN.md` - Technical refactoring details
- `Classical_Inputs_8_Pillars_standalone.tex` - Classical mathematical inputs


