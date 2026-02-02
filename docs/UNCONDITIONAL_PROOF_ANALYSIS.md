# Analysis: Path to Fully Unconditional Proof

## Current State

The theorem `hodge_conjecture'` has signature:
```lean
theorem hodge_conjecture' {p : ℕ}
    [CycleClass.PoincareDualFormExists n X p] 
    [SpineBridgeData n X p]
    [CalibratedCurrentRegularityData n X (2 * (n - p))]
    [ChowGAGAData n X]
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_rational : isRationalClass (ofForm γ h_closed)) 
    (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : SignedAlgebraicCycle n X p), Z.cycleClass_geom = ofForm γ h_closed
```

## Blockers to Unconditional Proof

### 1. `PoincareDualFormExists` (FUNDAMENTAL BLOCKER)

**What it requires**: A function `choose : (Z : Set X) → PoincareDualFormData n X p Z` that
returns a closed (2p)-form representing the Poincaré dual of Z for ANY set Z.

**Why it's hard**: Computing the Poincaré dual form requires:
1. Integration current theory (defining [Z] as a homology class)
2. Poincaré duality theorem (existence of dual cohomology class)
3. De Rham comparison (representing cohomology by smooth forms)
4. Hodge theory (selecting the unique harmonic representative)

**Current approach**: No instance exists. The definition of `cycleClass_geom` bakes in
the dependency on this typeclass.

### 2. `SpineBridgeData` (DEPENDS ON #1)

**What it requires**: Proof that for all SignedAlgebraicCycle Z:
```
Z.cycleClass_geom = ofForm Z.representingForm Z.representingForm_closed
```

**Why it's hard**: This requires proving that for our specific construction (Harvey-Lawson
from a cone-positive form γ), the Poincaré dual of the support equals γ.

**Mathematical content**: For a calibrated current T constructed from γ, with support Z:
- The integration current [Z] represents the homology class PD([γ])
- Therefore, the Poincaré dual of Z is [γ]
- Hence FundamentalClassSet(Z) = γ (up to cohomology)

This is the key theorem of calibration theory / GMT.

### 3. `ChowGAGAData` (EASIER BUT STILL BLOCKING)

**What it requires**: Proof that `IsAnalyticSet → IsAlgebraicSet` on projective varieties.

**Current state**: 
- `IsAnalyticSet` is properly defined (local holomorphic zero loci) ✓
- `IsAlgebraicSet := IsClosed` is STILL A STUB ✗

**Why it matters**: Even if we provide an instance, using `IsAlgebraicSet := IsClosed` 
would be a semantic gotcha - it makes Chow/GAGA trivially true by weakening the notion
of algebraic set.

### 4. `CalibratedCurrentRegularityData` (NOT IN AUDIT BAD LIST)

**Observation**: This typeclass is NOT in the audit's "bad binders" regex. Even if we
eliminate the other 3, it would remain in the signature but not fail the audit.

**Mathematical content**: Harvey-Lawson regularity theorem - the support of a calibrated
current is an analytic variety.

## Why These Cannot Be Eliminated Easily

### The Fundamental Issue

The definition of `cycleClass_geom` is:
```lean
def cycleClass_geom [PoincareDualFormExists] := 
  ofForm (FundamentalClassSet support) ...
```

This COMPUTES the cohomology class from the support via Poincaré duality.

The playbook requires:
> `cycleClass_geom` must be the **geometric** class from the **fundamental class / 
> integration current of the support**, not an alias of `cycleClass`.

This means we CANNOT redefine `cycleClass_geom` to use a carried form instead.

But COMPUTING the geometric class requires Poincaré duality infrastructure that
doesn't exist.

### The Circularity

1. To eliminate `PoincareDualFormExists`, we need a global instance
2. A global instance requires returning the CORRECT form for any set
3. The correct form is the Poincaré dual, which requires Hodge theory
4. We don't have Hodge theory formalized

## What Would Be Required

### Option A: Implement Hodge Theory (Months of Work)

1. Define Laplacian on forms: Δ = d∘δ + δ∘d
2. Prove elliptic regularity: Δω = 0 has smooth solutions
3. Prove Hodge decomposition: Ω^k = Harmonic ⊕ Exact ⊕ Coexact
4. Prove finite-dimensionality of harmonic forms
5. Construct Poincaré dual via harmonic representative

**Estimated effort**: 3000-8000 lines of new Lean code
**Prerequisites**: Sobolev spaces on manifolds, elliptic PDE theory

### Option B: Weaken the Theorem Statement (FORBIDDEN)

Change `cycleClass_geom` to use a carried form instead of computing from support.
This is explicitly forbidden by the playbook.

### Option C: Accept Current State (AUDIT FAILS)

The current formalization represents a CONDITIONAL proof:
> IF Poincaré duality holds AND calibration theory works AND Chow/GAGA holds
> THEN the Hodge Conjecture is true

This is mathematically valid - it shows the logical structure of the proof.
The deep results are made EXPLICIT as typeclass assumptions rather than hidden.

## Conclusion

To make the audit pass without adding axioms/stubs/sorries requires implementing
substantial mathematical infrastructure (Hodge theory, GMT) that would take
months of focused effort.

The current state is "mathematically honest" - all assumptions are explicit.
The audit correctly identifies that these are deep assumptions, not proven theorems.

## Verification Commands

```bash
# Build succeeds
./scripts/build.sh

# No sorry in codebase
grep -RIn --include="*.lean" "^[[:space:]]*sorry\b" Hodge/ | grep -v Quarantine

# No custom axioms
grep -RIn --include="*.lean" "^[[:space:]]*axiom\b" Hodge/ | grep -v Quarantine

# Kernel axioms are clean
lake env lean Hodge/Utils/DependencyCheck.lean

# Audit fails (due to deep typeclass binders)
./scripts/audit_practical_unconditional.sh
```
