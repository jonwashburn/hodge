# Stage 6 (C): Cohomology Rationality Survey

## Overview

This document surveys the current state of cohomology support in this Hodge conjecture formalization and provides recommendations for improving the definition of rational classes to better align with standard mathematical foundations.

## Current State Analysis

### De Rham Cohomology Implementation

The project has a well-developed de Rham cohomology implementation in `Hodge/Cohomology/Basic.lean`:

**Key Definitions:**
- `DeRhamCohomologyClass n X k`: Quotient of closed k-forms by exact k-forms
- `Cohomologous`: Equivalence relation for cohomology (ω₁ ~ ω₂ iff ω₁ - ω₂ is exact)
- Algebraic structure: AddCommGroup, Module ℂ, cup product via wedge

**Algebraic Properties (PROVEN):**
- Cup product is distributive: `mul_add`, `add_mul`
- Compatible with scalar multiplication: `mul_smul`, `smul_mul`
- Unit element exists: `unitClass` with `one_mul`, `mul_one` (up to degree casts)
- Associativity is NOT proven (requires `smoothWedge_assoc` which is off-track)

### Current Rational Classes Definition

The current `isRationalClass` is an inductive predicate with constructors:

```lean
inductive isRationalClass : DeRhamCohomologyClass n X k → Prop where
  | zero : isRationalClass 0
  | unit : isRationalClass unitClass
  | of_witness (ω) [IsRationalFormWitness n X k ω] : isRationalClass ⟦ω, _⟧
  | add : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂)
  | smul_rat (q : ℚ) : isRationalClass η → isRationalClass (q • η)
  | neg : isRationalClass η → isRationalClass (-η)
  | mul : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂)
```

**Strengths:**
- Algebraically closed (subring of de Rham cohomology)
- Non-degenerate (can declare rational witnesses via `IsRationalFormWitness`)
- Supports Kähler form rationality

**Weaknesses:**
- Not tied to actual H^*(X;ℚ) → H^*(X;ℝ) comparison map
- No connection to singular cohomology
- Purely axiomatic rather than constructive

## Mathlib Cohomology Support Analysis

### What’s missing / what exists in Mathlib (updated)

**Singular (co)homology:**

Mathlib does have **singular homology**:

- `Mathlib.AlgebraicTopology.SingularHomology.Basic`

However, a ready-to-use “singular cohomology” API may not be present as a first-class object in the same way,
so Stage 6 likely needs either:

- defining cohomology as the homology of the dual cochain complex, or
- using existing derived-functor/sheaf-cohomology infrastructure where appropriate.

**De Rham Theory:**
- No general de Rham cohomology in Mathlib
- Differential forms exist (`Mathlib.Analysis.DifferentialGeometry.DifferentialForm`)
- Exterior derivatives available
- No de Rham theorem (comparison with singular cohomology)

**Comparison Maps:**
- No H^*(X;ℚ) → H^*(X;ℝ) → H^*(X;ℂ) comparison isomorphisms
- No period maps or period matrices
- No Gauss-Manin connections

### What exists in Mathlib (relevant pieces)

**Algebraic Structure:**
- `Module ℚ`, `Module ℝ`, `Module ℂ` - base rings for coefficients
- Tensor products: `TensorProduct ℚ ℝ`, `TensorProduct ℚ ℂ`
- Linear algebra over different fields

**Topological foundations:**
- Manifold theory: `ChartedSpace`, `IsManifold`
- Fiber bundles and connections
- Integration theory on manifolds

**Algebraic geometry:**
- Schemes and varieties (but not specifically projective)
- Sheaf cohomology foundations
- Some Chern class theory

## Recommendations for Improved Rational Classes

### Option 1: Comparison Map Approach (Ideal)

Replace `isRationalClass` with a definition based on actual comparison maps:

```lean
-- Hypothetical improved definition
def RationalCohomologyClass (n : ℕ) (X : Type*) (k : ℕ) : Type* :=
  { α : DeRhamCohomologyClass n X k // 
    ∃ (β : SingularCohomologyClass X k ℚ), 
      comparisonMap β = (complexification ∘ realization) α }

-- Where:
-- comparisonMap : H^k(X;ℚ) → H^k_dR(X;ℂ) is the comparison isomorphism
-- realization : H^k_dR(X;ℂ) → H^k(X;ℂ) is de Rham realization  
-- complexification : H^k(X;ℚ) → H^k(X;ℂ) is ℚ → ℂ extension
```

**Advantages:**
- Mathematically precise and standard
- Connects to period theory and arithmetic geometry
- Natural for studying transcendence

**Disadvantages:**
- Requires implementing singular cohomology (~6 months)
- Requires proving de Rham theorem (~3-6 months)
- Major infrastructure investment

### Option 2: Lattice-Based Approach (Practical)

Improve the current system with better axiomatization:

```lean
-- Enhanced witness class with lattice structure
class RationalLatticeWitness (n : ℕ) (X : Type*) (k : ℕ) where
  -- ℚ-basis for rational cohomology in degree k
  rational_basis : Finset (DeRhamCohomologyClass n X k)
  -- Integrality conditions (periods lie in ℚ-span)
  basis_rational : ∀ α ∈ rational_basis, isRationalClass α
  -- Span property: every rational class is ℚ-linear combination
  rational_span : ∀ α, isRationalClass α ↔ α ∈ ℚ-span rational_basis
  
-- Improved rational class definition
def isRationalClass' (α : DeRhamCohomologyClass n X k) : Prop :=
  α ∈ ℚ-span (RationalLatticeWitness.rational_basis (n:=n) (X:=X) (k:=k))
```

**Advantages:**
- More structured than pure inductive approach
- Connects to classical period theory
- Maintains current proof compatibility

**Disadvantages:**
- Still axiomatic rather than constructive
- Requires choosing canonical bases

### Option 3: Cycle Class Approach (Geometric)

Focus on the geometric source of rational classes:

```lean
-- Rational classes via algebraic cycles
class AlgebraicCycleClass (n : ℕ) (X : Type*) (k : ℕ) 
  (Z : AlgebraicCycle X (k/2)) where  -- k must be even for cycles
  -- Integration current [Z] ∈ H_k(X;ℤ)
  integration_current : DeRhamCurrent n X k
  -- Poincaré duality: [Z] ↦ cohomology class
  poincare_dual : DeRhamCohomologyClass n X (2*n - k)
  -- Rationality: cycle classes are rational
  cycle_rational : isRationalClass poincare_dual

-- Rational classes from algebraic geometry
def isRationalClass_geometric (α : DeRhamCohomologyClass n X k) : Prop :=
  ∃ (cycles : List (AlgebraicCycleClass n X k)), 
    α = ∑ (c ∈ cycles), (rational_coeff c) • c.poincare_dual
```

**Advantages:**
- Geometrically motivated (Hodge conjecture context)
- Connects rational classes to actual algebraic cycles
- Natural for projective varieties

**Disadvantages:**
- Requires substantial algebraic geometry (cycles, intersection theory)
- Complex to implement in Lean

## Specific Action Items

### Short Term (1-2 weeks)

1. **Documentation**: Create detailed comments explaining the current `isRationalClass` 
   - Mathematical motivation (comparison maps)
   - Relation to period matrices
   - Connection to transcendence theory

2. **Enhanced Witnesses**: Improve `IsRationalFormWitness` with:
   - Geometric examples (Chern classes, cycle classes)
   - Compatibility with cup products
   - Period integrality conditions

3. **Better Testing**: Add examples showing `isRationalClass` is non-degenerate:
   - Kähler form witnesses
   - Hyperplane section classes
   - Verification that not all classes are rational

### Medium Term (1-2 months)

1. **Lattice Structure**: Implement Option 2 above:
   - `RationalLatticeWitness` type class
   - Finite-dimensional ℚ-vector space structure
   - Period matrix computations

2. **Compatibility**: Prove the enhanced definition matches current `isRationalClass`
   - Equivalence for common examples
   - Preservation of algebraic structure
   - Migration path for existing proofs

### Long Term (6+ months)

1. **Singular Cohomology**: Implement basic singular cohomology theory
   - CW complexes and cellular cohomology
   - Comparison with simplicial cohomology
   - Universal coefficient theorems

2. **De Rham Theorem**: Prove de Rham isomorphism
   - H^*_dR(X;ℝ) ≅ H^*(X;ℝ) for smooth manifolds
   - Compatibility with cup products and Poincaré duality
   - Extension to complex coefficients

3. **Full Comparison Theory**: Implement Option 1
   - Complete comparison isomorphisms
   - Period domains and period maps
   - Transcendence criteria

## Mathematical Context: The Comparison Isomorphism

### Classical Theory

For a smooth projective variety X over ℂ, there are canonical isomorphisms:

```
H^k(X;ℚ) ⊗_ℚ ℂ ≅ H^k_dR(X;ℂ) ≅ H^k(X^an;ℂ)
```

Where:
- H^k(X;ℚ) = singular cohomology with rational coefficients
- H^k_dR(X;ℂ) = de Rham cohomology (holomorphic + antiholomorphic forms)
- H^k(X^an;ℂ) = singular cohomology of analytic topology

### Rationality Definition

A de Rham class α ∈ H^k_dR(X;ℂ) is **rational** iff α lies in the image of:
```
H^k(X;ℚ) ⊗_ℚ ℂ → H^k_dR(X;ℂ)
```

This is equivalent to α having **rational periods**: for any topological k-cycle γ,
```
∫_γ α ∈ ℚ · (base periods)
```

### Hodge Conjecture Connection

The Hodge conjecture states that rational (p,p)-classes come from algebraic cycles:
- Every rational α ∈ H^{2p}(X;ℚ) ∩ H^{p,p}(X) is a ℚ-linear combination of cycle classes
- This is where rationality becomes crucial for the conjecture

## Conclusion: The `cohomology_survey` Target

Based on this analysis, the main work for eliminating `sorry` or `axiom` at `cohomology_survey` involves:

1. **Creating this survey document** ✓ (this document)
2. **Documenting Mathlib gaps** ✓ (above analysis)  
3. **Proposing concrete improvements** ✓ (three options presented)
4. **Providing implementation roadmap** ✓ (action items)

The current `isRationalClass` definition, while imperfect, serves its purpose in the Hodge conjecture formalization. The main limitation is the lack of connection to singular cohomology, but this can be addressed incrementally through the proposed lattice-based approach (Option 2) without requiring massive infrastructure changes.

## Implementation Status

- **Current `isRationalClass`**: Functional but axiomatically based
- **Mathlib singular cohomology**: Not available (major gap)
- **De Rham comparison**: Not formalized (major gap)
- **Geometric cycle classes**: Partially available via `integrationCurrent_data` infrastructure
- **Recommendation**: Proceed with Option 2 (lattice-based improvement) as a practical next step

---

**Note**: This document replaces any `sorry` or `axiom` at the `cohomology_survey` target by providing a comprehensive analysis of the mathematical and implementation issues around rational cohomology classes in the Hodge conjecture formalization.
