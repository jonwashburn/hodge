# P1: Prove `harveyLawson_represents_witness`

**Re-queue this prompt until the axiom is eliminated.**

## Cursor Notes

```
# Hodge Conjecture Lean 4 Formalization

## CRITICAL: Mathlib Cache (NEVER rebuild Mathlib from source!)
Before running ANY `lake build` command, ALWAYS run:
  lake exe cache get

## Build Commands
  ./scripts/build.sh           # Safe build with cache
  lake env lean <file.lean>    # Check single file
  lake build Hodge.Kahler.Main # Build main theorem

## Verification Commands
  lake env lean Hodge/Utils/DependencyCheck.lean  # Check axioms
  ./scripts/audit_stubs.sh                        # Full audit

## Key Files for This Task
  - Hodge/Kahler/Main.lean                 # THE AXIOM TO ELIMINATE
  - Hodge/Classical/HarveyLawson.lean      # Harvey-Lawson infrastructure
  - Hodge/Classical/CycleClass.lean        # FundamentalClassSet
  - Hodge/GMT/PoincareDuality.lean         # GMT bridge
  - Hodge/Analytic/Currents.lean           # Current infrastructure
```

## The Axiom

**File**: `Hodge/Kahler/Main.lean` (lines 232-238)

```lean
private axiom harveyLawson_represents_witness {p : ℕ}
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (Zpos : Set X) (h_alg : isAlgebraicSubvariety n X Zpos) :
    ofForm γ h_closed =
      ofForm (FundamentalClassSet n X p (Zpos ∪ ∅))
             (FundamentalClassSet_isClosed p (Zpos ∪ ∅)
               (Set.union_empty Zpos ▸ FundamentalClassSet_isClosed_support h_alg))
```

## What This Axiom Says (Mathematically)

Given:
- A closed (p,p)-form γ on a compact Kähler manifold X
- An algebraic subvariety Zpos of codimension p
- The fact that Zpos came from Harvey-Lawson applied to a calibrated current representing γ

**Conclusion**: The cohomology class of γ equals the fundamental class of Zpos:
```
[γ] = [Zpos]   in H^{2p}(X, ℂ)
```

## Why This Is True (Mathematical Proof Sketch)

The proof requires connecting several pieces:

### Step 1: Harvey-Lawson Structure Theorem
Given a calibrated integral current T (representing a Hodge class),
Harvey-Lawson produces analytic subvarieties V₁,...,Vₘ with multiplicities m₁,...,mₘ such that:
```
T = Σᵢ mᵢ [Vᵢ]
```
where [Vᵢ] is the integration current over Vᵢ.

### Step 2: Regularization Theorem  
The integration current [Vᵢ] can be regularized to give a smooth closed form ηᵢ
representing the same cohomology class:
```
[T|ηᵢ] = [Vᵢ]   in H^{2p}(X, ℂ)
```

### Step 3: Cohomology Comparison
Since T represents γ (as a current), and the integration currents over Vᵢ
together represent T, we have:
```
[γ] = [T] = [Σᵢ mᵢ [Vᵢ]] = Σᵢ mᵢ [Vᵢ]
```

### Step 4: For Our Case
In `cone_positive_produces_cycle`, we set Zpos to be the whole support variety
from Harvey-Lawson. Since we're in the "positive cone" case with a single variety
of multiplicity 1:
```
[γ] = [Zpos]
```

## Implementation Approach Options

### Option A: Full GMT Implementation (Recommended for Mathlib-quality)
1. Define proper regularization of integration currents
2. Prove integration currents descend to cohomology
3. Prove Harvey-Lawson decomposition respects cohomology
4. Chain the results

**Estimated effort**: 200-500 lines of Lean, requires GMT expertise

### Option B: Axiomatize at a Higher Level
Replace this axiom with a cleaner mathematical statement:
```lean
axiom HarveyLawson.integration_represents_form {T : IntegralCurrent}
    (hT : isCalibrated T ω) (hV : HarveyLawsonOutput T V) :
    [T] = [V] in DeRhamCohomology
```

This pushes the axiom to a more natural mathematical boundary.

**Estimated effort**: 50-100 lines, cleaner statement but still an axiom

### Option C: Prove from Existing Infrastructure
Trace what's needed from the current infrastructure:
1. `integration_current` is already wired to real measures
2. `gmt_cycle_to_cohomology_path` exists in `GMT/PoincareDuality.lean`
3. `FundamentalClassSet` is Z-dependent

Try to close the gap using existing definitions.

**Estimated effort**: 100-200 lines, may reveal missing lemmas

## Definition of Done

- [ ] `harveyLawson_represents_witness` is changed from `axiom` to `theorem`
- [ ] OR: the axiom is replaced with a mathematically cleaner statement
- [ ] `lake build Hodge.Kahler.Main` succeeds
- [ ] `lake env lean Hodge/Utils/DependencyCheck.lean` shows fewer custom axioms

## Verification Command

```bash
lake env lean Hodge/Utils/DependencyCheck.lean 2>&1 | grep -i harveylawson
```

Should return nothing when complete.

## Progress Log

(Add entries as you work)

- [ ] Started investigation
- [ ] Identified which infrastructure is missing
- [ ] Chose implementation approach
- [ ] Implemented solution
- [ ] Verified build passes
- [ ] Verified axiom is eliminated

---
**Status (2026-01-24)**: P2 was eliminated as an independent axiom (it is now a theorem derived
from P1). **P1 is now the ONLY remaining proof-track custom axiom.**
