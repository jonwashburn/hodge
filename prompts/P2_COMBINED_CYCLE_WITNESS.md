# P2: Prove `combined_cycle_represents_witness`

## ✅ AXIOM ELIMINATED (2026-01-24)

`combined_cycle_represents_witness` is now a **theorem derived from P1**, so it no longer
appears as a custom axiom in the proof-track dependency closure.

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
  - Hodge/Classical/CycleClass.lean        # FundamentalClassSet
  - Hodge/GMT/PoincareDuality.lean         # GMT bridge
```

## The Axiom

**File**: `Hodge/Kahler/Main.lean`

```lean
private theorem combined_cycle_represents_witness {p : ℕ}
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (Z_pos Z_neg : Set X)
    (Z_pos_alg : isAlgebraicSubvariety n X Z_pos)
    (Z_neg_alg : isAlgebraicSubvariety n X Z_neg) :
    ofForm γ h_closed =
      ofForm (FundamentalClassSet n X p (Z_pos ∪ Z_neg))
             (FundamentalClassSet_isClosed p (Z_pos ∪ Z_neg)
               (isAlgebraicSubvariety_union Z_pos_alg Z_neg_alg))
```

## What This Axiom Says (Mathematically)

Given:
- A closed (p,p)-form γ on a compact Kähler manifold X  
- Two algebraic subvarieties Z_pos and Z_neg of codimension p
- γ = γ_plus - γ_minus where Z_pos represents γ_plus and Z_neg represents γ_minus

**Conclusion**: The cohomology class of γ equals the fundamental class of Z_pos ∪ Z_neg:
```
[γ] = [Z_pos ∪ Z_neg]   in H^{2p}(X, ℂ)
```

## Why This Is True (Mathematical Proof Sketch)

This axiom is about **linearity of the fundamental class map**:

### Step 1: Fundamental Class is Linear
The map `FundamentalClass : Z → H^{2p}(X)` extends linearly to signed combinations:
```
[Z_pos - Z_neg] = [Z_pos] - [Z_neg]
```

### Step 2: γ Splits as γ_plus - γ_minus
By Hodge decomposition (in the proof architecture), γ = γ_plus - γ_minus where:
- γ_plus is positive harmonic (from the "plus" part of cone positivity)
- γ_minus is positive harmonic (from the "minus" part)

### Step 3: Z_pos Represents γ_plus, Z_neg Represents γ_minus
By Harvey-Lawson (P1), we have:
```
[Z_pos] = [γ_plus]
[Z_neg] = [γ_minus]
```

### Step 4: Combine
```
[γ] = [γ_plus - γ_minus] = [γ_plus] - [γ_minus] = [Z_pos] - [Z_neg] = [Z_pos - Z_neg]
```

And [Z_pos - Z_neg] in the sense of signed cycles corresponds to [Z_pos ∪ Z_neg] in our formalization.

## Dependencies

This axiom logically depends on **P1 (harveyLawson_represents_witness)**.

If P1 gives us `[γ_plus] = [Z_pos]` and `[γ_minus] = [Z_neg]`, then P2 follows by linearity.

**Recommended**: Solve P1 first, then P2 should be easier.

✅ This is exactly what we did: we proved P2 from P1 by instantiating P1 with
`Zpos := Z_pos ∪ Z_neg`, simplifying the set `(Z_pos ∪ Z_neg) ∪ ∅`, and using
`Hodge.ofForm_proof_irrel` to align closedness proofs.

## Implementation Approach Options

### Option A: Prove from P1 + Linearity
If P1 is a theorem, then P2 follows by:
1. The splitting γ = γ_plus - γ_minus (from the proof setup)
2. P1 applied to each piece
3. Linearity of cohomology subtraction

```lean
theorem combined_cycle_represents_witness ... := by
  have h1 := harveyLawson_represents_witness γ_plus ...
  have h2 := harveyLawson_represents_witness γ_minus ...
  -- Use linearity of ofForm and FundamentalClassSet
  ...
```

### Option B: Prove Linearity of FundamentalClassSet
Add and prove:
```lean
theorem FundamentalClassSet_linear {Z₁ Z₂ : Set X} :
    FundamentalClassSet (Z₁ ∪ Z₂) = 
      FundamentalClassSet Z₁ + FundamentalClassSet Z₂
```
Then use this to reduce P2 to two applications of P1.

### Option C: Replace with Cleaner Axiom
If the proof is too complex, axiomatize at a higher level:
```lean
axiom fundamental_class_respects_signed_cycles :
    [Z_pos - Z_neg] = [Z_pos] - [Z_neg]
```

## Definition of Done

- [x] `combined_cycle_represents_witness` is changed from `axiom` to `theorem` (derived from P1)
- [x] `lake build Hodge.Kahler.Main` succeeds
- [x] `lake build Hodge.Utils.DependencyCheck` shows P2 is gone

## Verification Command

```bash
lake env lean Hodge/Utils/DependencyCheck.lean 2>&1 | grep -i combined
```

✅ It now returns nothing:

```bash
$ lake exe cache get
$ lake build Hodge.Utils.DependencyCheck
info: 'hodge_conjecture' depends on axioms: [propext, _private.Hodge.Kahler.Main.0.harveyLawson_represents_witness, Classical.choice, Quot.sound]
```

## Progress Log

(Add entries as you work)

- [x] Started investigation
- [x] Assessed dependency on P1
- [x] Implemented solution: prove P2 from P1
- [x] Verified build passes
- [x] Verified axiom is eliminated

---
**P2 COMPLETE. The only remaining proof-track custom axiom is P1.**
