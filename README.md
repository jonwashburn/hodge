# Hodge Conjecture Formalization in Lean 4

This repo contains a **Lean 4 proof skeleton** inspired by the manuscript `Hodge-v6-w-Jon-Update-MERGED.tex`.

Important: it is **not yet a faithful formalization of the classical Hodge conjecture** as mathematicians state it. Several core notions are currently stubbed/opaque, and the current Lean “main theorem” is intentionally weaker than the classical conjecture.

## Main Theorem (current Lean statement)

The main result is formalized in `Hodge/Kahler/Main.lean`:

```lean
theorem hodge_conjecture' {p : ℕ} (γ : SmoothForm n X (2 * p))
    (h_rational : isRationalClass γ) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : Set X), isAlgebraicSubvariety n X Z
```

**Warning (statement weakness):** this conclusion currently does **not** relate the produced algebraic object back to the input class \([\gamma]\) (there is no `RepresentsClass` / fundamental-class equality in the statement).

## Status (local checks)

- **Sorries in `Hodge/**/*.lean`:** 0 (checked via grep)
- **Declared `axiom` in `Hodge/**/*.lean`:** 50 (checked via grep)
- **Full `lake build`:** not rerun in this session (running full builds is intentionally avoided)

## Axiom Dependencies

### Direct Dependencies of `hodge_conjecture'`

Reproduce:

```bash
lake env lean DependencyCheck.lean
```

Current output:

```
#print axioms hodge_conjecture'
'hodge_conjecture'' depends on axioms: [
  cohomologous_refl,
  cohomologous_symm,
  cohomologous_trans,
  exists_uniform_interior_radius,
  flat_limit_of_cycles_is_cycle,
  harvey_lawson_theorem,
  isRationalClass_add,
  isRationalClass_smul_rat,
  microstructureSequence_are_cycles,
  propext,
  serre_gaga,
  zero_is_pq,
  zero_is_rational_axiom,
  Classical.choice,
  Quot.sound
]
```

## Faithfulness / “proof killers” (current)

The Lean development is not yet a faithful Hodge formalization primarily because:

- **Final statement is too weak**: it produces an “algebraic subvariety” but does not assert it represents \([\gamma]\).
- **Core predicates are opaque/stubbed**: e.g. `isRationalClass`, `isPPForm'`, and the algebraicity predicate used by `isAlgebraicSubvariety`.
- **Key analytic/GMT steps are axiomatized**: e.g. `microstructureSequence_are_cycles`, `harvey_lawson_theorem`, and `flat_limit_of_cycles_is_cycle`.

## Project Structure

```
Hodge/
├── Basic.lean              # Core definitions: complex manifolds, Kähler manifolds
├── Main.lean               # Final integration and bridge axioms
├── Analytic/               # Geometric measure theory
│   ├── Forms.lean          # Differential forms
│   ├── Currents.lean       # Currents and boundary operator
│   ├── IntegralCurrents.lean  # Integral currents
│   ├── Calibration.lean    # Calibrated geometry
│   ├── FlatNorm.lean       # Flat norm topology
│   ├── Norms.lean          # L2 and comass norms
│   ├── Grassmannian.lean   # Calibrated Grassmannian
│   └── SheafTheory.lean    # Sheaf-theoretic infrastructure
├── Kahler/                 # Kähler geometry
│   ├── Manifolds.lean      # Kähler manifold structure and rationality
│   ├── TypeDecomposition.lean  # Hodge (p,q)-decomposition
│   ├── Cone.lean           # Strongly positive cones
│   ├── SignedDecomp.lean   # Signed cycle decomposition
│   ├── Microstructure.lean # Cubulation and microstructure sequences
│   └── Main.lean           # Main theorem proof integration
├── Classical/              # Classical algebraic geometry
│   ├── Bergman.lean        # Bergman spaces, jet bundles
│   ├── SerreVanishing.lean # Serre vanishing theorem
│   ├── GAGA.lean           # GAGA correspondence
│   ├── HarveyLawson.lean   # Harvey-Lawson theorem
│   ├── Lefschetz.lean      # Hard Lefschetz theorem
│   └── FedererFleming.lean # Federer-Fleming compactness
└── Utils/
    └── BaranyGrinberg.lean # Barany-Grinberg theorem (calibration theory)
```

## Statistics

| Metric | Count |
|--------|-------|
| Declared axioms (`^axiom` in `Hodge/**/*.lean`) | 50 |
| Sorry statements | 0 |
| Lean files | 21 |
| Lines of code | ~5500 |

## Key References

1. **Hodge Theory**: P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978.
2. **Calibrated Geometry**: R. Harvey and H.B. Lawson Jr., "Calibrated geometries", *Acta Math.* 148 (1982), 47-157.
3. **Geometric Measure Theory**: H. Federer, *Geometric Measure Theory*, Springer, 1969.
4. **GAGA**: J-P. Serre, "Géométrie algébrique et géométrie analytique", *Ann. Inst. Fourier* 6 (1956), 1-42.
5. **Hodge Conjecture**: C. Voisin, *Hodge Theory and Complex Algebraic Geometry*, Vols. I & II, Cambridge, 2002-2003.
6. **Hard Lefschetz**: S. Lefschetz, *L'analysis situs et la géométrie algébrique*, Gauthier-Villars, 1924.
7. **Federer-Fleming**: H. Federer and W.H. Fleming, "Normal and integral currents", *Ann. of Math.* 72 (1960), 458-520.
8. **Tian**: G. Tian, "On a set of polarized Kähler metrics", *J. Differential Geom.* 32 (1990), 99-130.

## Definition of Unconditional Proof

At present, the repo has **0 `sorry`** but still uses **many axioms/opaque placeholders**, so “unconditional proof of the classical Hodge conjecture” is **not** an accurate description of the current Lean artifact.

## License

This project is open source. Mathematical content is based on established results in algebraic and complex geometry.
