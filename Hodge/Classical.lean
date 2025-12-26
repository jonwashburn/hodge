/-!
# Track A: Classical Axioms Foundation

This module exports all the classical axioms needed for the Hodge Conjecture proof.
These are deep theorems from complex geometry, algebraic geometry, and
geometric measure theory that are not (yet) in Mathlib.

## Contents

1. **HarveyLawson**: Calibrated currents → analytic subvarieties
2. **GAGA**: Analytic subvarieties → algebraic subvarieties (projective case)
3. **FedererFleming**: Compactness of integral currents in flat norm
4. **Lefschetz**: Hard Lefschetz theorem (cohomology isomorphism)
5. **Bergman**: Bergman kernel asymptotics (Tian's theorem)
6. **SerreVanishing**: Higher cohomology vanishes for ample powers

## Philosophy

Each axiom is stated with:
- A structured hypothesis type (not raw Props)
- A structured conclusion type
- Full documentation citing the original reference
- Clear contracts for what is assumed

The goal is that these axioms could be replaced with proofs as Mathlib grows,
or remain as trusted axioms with explicit, auditable assumptions.

## Usage

```lean
import Hodge.Classical

-- Access any axiom
#check harvey_lawson_theorem
#check serre_gaga
#check federer_fleming_compactness
#check hard_lefschetz
#check tian_convergence
#check serre_vanishing
```
-/

-- Import all classical axioms
import Hodge.Classical.HarveyLawson
import Hodge.Classical.GAGA
import Hodge.Classical.FedererFleming
import Hodge.Classical.Lefschetz
import Hodge.Classical.Bergman
import Hodge.Classical.SerreVanishing

/-! ## Summary of Axioms

| Axiom | Type | Reference |
|-------|------|-----------|
| `harvey_lawson_theorem` | Calibrated → Analytic | Harvey-Lawson 1982 |
| `serre_gaga` | Analytic → Algebraic | Serre 1956 |
| `federer_fleming_compactness` | Mass-bounded → Convergent | Federer-Fleming 1960 |
| `hard_lefschetz` | L^{n-p} is bijective | Griffiths-Harris 1978 |
| `tian_convergence` | Bergman → Kähler in C² | Tian 1990 |
| `serre_vanishing` | H^q(L^M ⊗ F) = 0 for q > 0, M ≫ 0 | Serre 1955 |

These form the classical backbone of the proof.
-/
