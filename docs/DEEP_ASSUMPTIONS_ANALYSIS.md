# Deep Assumptions Analysis

## Current State (2026-02-01, Phase 8 Update)

The Hodge Conjecture formalization has the following status:

| Criterion | Status |
|-----------|--------|
| No `sorry` blocks | ✅ PASS |
| No custom `axiom` declarations | ✅ PASS |
| No custom `opaque` declarations | ✅ PASS |
| No `instance … .universal` on instance line | ✅ PASS |
| Kernel axioms | ✅ Only `propext`, `Classical.choice`, `Quot.sound` |
| Deep typeclass binders in `hodge_conjecture'` | ❌ FAIL (4 binders) |

The audit `./scripts/audit_practical_unconditional.sh` **fails** because `hodge_conjecture'` requires **four** deep typeclasses:
1. `[CycleClass.PoincareDualFormExists n X p]` - de Rham representability
2. `[SpineBridgeData n X p]` - Harvey-Lawson bridge theorem
3. `[CalibratedCurrentRegularityData n X (2 * (n - p))]` - Harvey-Lawson regularity
4. `[ChowGAGAData n X]` - Chow/GAGA theorem

### Phase 8 Semantic Restorations Completed

| Definition | Before | After |
|------------|--------|-------|
| `IsAnalyticSet` | `IsClosed` (stub) | `IsAnalyticSetZeroLocus` (local holomorphic zero locus) |
| `cycleClass_geom` | Alias of `cycleClass` | `ofForm (FundamentalClassSet support)` |
| `ChowGAGAData` | Trivial universal instance | Explicit typeclass (no instance) |
| `CalibratedCurrentRegularityData` | N/A | New explicit typeclass |

### Why This Is Mathematically Honest

The deep typeclass binders are NOT semantic stubs. They represent genuine mathematical content that:
1. Cannot be proved without substantial GMT/Hodge theory infrastructure
2. Make the assumptions EXPLICIT rather than hiding them in definitions
3. Allow the audit to correctly identify what remains to be formalized

## Why These Typeclasses Exist

These are **not semantic stubs**. They represent genuine mathematical content:

### `PoincareDualFormExists`

**Mathematical Content**: For every algebraic set Z of codimension p on a compact Kähler manifold X, there exists a closed (2p)-form η_Z (the "Poincaré dual form") such that:

```
∫_X η_Z ∧ α = ∫_Z α   for all closed (2n-2p)-forms α
```

This is the **de Rham representability theorem** for integration currents. It says that the linear functional "integration over Z" can be represented by a smooth differential form.

**Why It's Hard**: Proving this requires:
1. **Finite-dimensionality of cohomology**: H^k(X, ℂ) is finite-dimensional (Hodge theory)
2. **Non-degeneracy of pairing**: The cohomology pairing ⟨α, β⟩ = ∫_X α ∧ β is non-degenerate (Poincaré duality)
3. **Linear algebra inversion**: Given these, the Poincaré dual form exists by Riesz representation

None of these are in Mathlib for general Kähler manifolds.

### `SpineBridgeData`

**Mathematical Content**: For algebraic cycles Z constructed by the proof spine (via Harvey-Lawson + GAGA), the geometric fundamental class of Z's support equals the representing form class:

```
[FundamentalClassSet(Z.support)] = [Z.representingForm]
```

This is the **Harvey-Lawson bridge theorem**. It connects the geometric cycle class (from integration) with the algebraic cycle class (from the representing form).

**Why It's Hard**: Proving this requires:
1. **Calibration theory**: For calibrated currents, the mass equals the integral of the calibration form
2. **Cycle class computation**: The cycle class of a calibrated current equals the calibration form class
3. **Support analysis**: The support of the Harvey-Lawson output has the correct fundamental class

This requires deep GMT (Geometric Measure Theory) infrastructure not in Mathlib.

### `CalibratedCurrentRegularityData` (NEW in Phase 8)

**Mathematical Content**: For any calibrated integral current T with calibrating form ψ, the support of T is an analytic set (locally the zero locus of holomorphic functions).

```
∀ T ψ hcal, IsAnalyticSetZeroLocus (Current.support T)
```

This is the **Harvey-Lawson regularity theorem**. It says that calibrated currents have "nice" support that is analytically defined, not just topologically closed.

**Why It's Hard**: Proving this requires:
1. **GMT regularity theory**: Calibrated currents minimize mass in their homology class
2. **Analytic continuation**: Minimal surfaces in Kähler manifolds are complex-analytic
3. **Local structure**: The support is locally a complex submanifold away from a singular set

**Reference**: [Harvey-Lawson, "Calibrated Geometries", Acta Math. 1982, Theorem 6.1]

### `ChowGAGAData` (Trivial instance REMOVED in Phase 8)

**Mathematical Content**: Every analytic subset of a projective variety is algebraic.

```
∀ Z, IsAnalyticSet Z → IsAlgebraicSet Z
```

This is **Chow's theorem** combined with **GAGA** (Géométrie Algébrique et Géométrie Analytique).

**Why It's Hard**: Proving this requires:
1. **Chow's theorem**: Analytic subvarieties of projective space are algebraic
2. **GAGA comparison**: Coherent analytic sheaves on projective varieties are algebraic
3. **Projective embedding**: Using the projective structure of X to apply Chow

**Reference**: [Serre, "GAGA", Ann. Inst. Fourier 6 (1956), 1-42]

## Remaining Semantic Stubs (Documented)

These are definitions that remain as stubs but are documented:

| Definition | Status | What's Needed |
|------------|--------|---------------|
| `IsAlgebraicSet` (projective polynomial zero loci) | DONE | Prove Chow/GAGA analytic → algebraic |
| `buildSheetsFromConePositive := ∅` | STUB | Full microstructure sheet construction |

These stubs are **not on the main proof track** in the sense that they don't directly appear in `hodge_conjecture'`. However, they affect the construction of cycles via `cone_positive_produces_cycle`.

## What Would Be Needed

To eliminate these deep typeclass binders, one would need to formalize:

### Path 1: Full Hodge Theory

1. **Laplacian on forms**: Define Δ = d δ + δ d using the Hodge star
2. **Harmonic forms**: Ker(Δ) represents cohomology classes
3. **Hodge decomposition**: Ω^k = Harmonic ⊕ d(Ω^{k-1}) ⊕ δ(Ω^{k+1})
4. **Finite-dimensionality**: Ker(Δ) is finite-dimensional (elliptic theory)
5. **Poincaré duality**: The pairing descends to a non-degenerate pairing on cohomology

**Estimated effort**: 2000-5000 lines of new Lean code, requires:
- Sobolev spaces on manifolds
- Elliptic PDE theory
- Spectral theory for self-adjoint operators

### Path 2: Algebraic Cycle Class Map

1. **Chow groups**: CH^p(X) = algebraic cycles / rational equivalence
2. **Cycle class map**: cl: CH^p(X) → H^{2p}(X, ℤ) ⊂ H^{2p}_{dR}(X)
3. **Properties**: cl is a ring homomorphism, compatible with pullback/pushforward
4. **Well-definedness**: Show cl is independent of representative

**Estimated effort**: 1000-3000 lines, requires:
- Algebraic geometry infrastructure (schemes, Chow groups)
- Comparison theorems (algebraic vs analytic de Rham)

### Path 3: Direct GMT Construction

1. **Tubular neighborhoods**: For smooth submanifolds, construct neighborhoods
2. **Thom forms**: Construct "bump forms" supported near Z
3. **Regularity**: Extend to singular varieties via resolution
4. **Poincaré dual**: Show the Thom form satisfies the integration identity

**Estimated effort**: 1500-4000 lines, requires:
- Differential topology (tubular neighborhoods)
- Bump functions on manifolds
- Resolution of singularities

## Current Architecture

The current formalization uses this architecture:

```
SignedAlgebraicCycle
    |
    |-- pos : Set X           (positive part)
    |-- neg : Set X           (negative part)
    |-- representingForm : SmoothForm  (carried form)
    |
    |-- cycleClass : DeRhamCohomologyClass
    |       := ofForm(representingForm)      ← algebraic
    |
    |-- cycleClass_geom : DeRhamCohomologyClass
    |       := ofForm(FundamentalClassSet(support))  ← geometric
    |           ↑
    |           requires PoincareDualFormExists
```

The bridge between `cycleClass` and `cycleClass_geom` is `SpineBridgeData`:
```
SpineBridgeData.fundamental_eq_representing:
    cycleClass_geom = cycleClass
```

## Recommendation

The formalization is in a **mathematically honest state**:
- The deep assumptions are explicit, not hidden
- The proof uses `SpineBridgeData.fundamental_eq_representing` (not `rfl`)
- The semantic definition of `cycleClass_geom` is correct

The audit failure correctly indicates that these deep theorems haven't been proved. This is the expected outcome without building significant new infrastructure.

**To complete the formalization fully**, one would need to:
1. Choose one of the three paths above
2. Build the required infrastructure (months of work)
3. Prove `PoincareDualFormExists` and `SpineBridgeData` from the developed theory
4. Remove them as explicit parameters from `hodge_conjecture'`

## References

- [de Rham, "Variétés Différentiables", 1955] - de Rham's theorem
- [Hodge, "The Theory and Applications of Harmonic Integrals", 1941] - Hodge theory
- [Griffiths-Harris, "Principles of Algebraic Geometry", 1978] - Cycle class map
- [Federer, "Geometric Measure Theory", 1969] - Integration currents
- [Harvey-Lawson, "Calibrated Geometries", 1982] - Calibration theory
