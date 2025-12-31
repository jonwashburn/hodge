import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Pi

/-!
# Bárány-Grinberg Rounding Lemma

This file contains the Bárány-Grinberg rounding lemma, a key result in
combinatorial geometry used in the SYR (Slicing, Yoking, Rounding) construction.

## Main Result

- `barany_grinberg`: Given vectors v₁, ..., vₘ in ℝᵈ with ‖vᵢ‖_∞ ≤ 1 and
  coefficients aᵢ ∈ [0, 1], there exist εᵢ ∈ {0, 1} such that
  ‖∑ (εᵢ - aᵢ) vᵢ‖_∞ ≤ d.

## References

* I. Bárány and V.S. Grinberg, "On some combinatorial questions in finite-
  dimensional spaces", Linear Algebra Appl. 41 (1981), 1-9.
* N. Bansal, "Constructive algorithms for discrepancy minimization",
  FOCS 2010, 3-10.
-/

open Set Convex
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- **Bárány-Grinberg Rounding Lemma** (1981/1982).
    Given vectors v₁, ..., vₘ in ℝᵈ with ‖vᵢ‖_∞ ≤ 1 and coefficients aᵢ ∈ [0, 1],
    there exist εᵢ ∈ {0, 1} such that ‖∑ (εᵢ - aᵢ) vᵢ‖_∞ ≤ d.
    References:
    - [I. Bárány and V.S. Grinberg, "On some combinatorial questions in finite-dimensional spaces", Linear Algebra Appl. 41 (1981), 1-9].
    - [I. Bárány and V.S. Grinberg, J. Combin. Theory Ser. A (1982)].

    This lemma is essential for the "Rounding" step of the SYR construction,
    allowing the conversion of continuous weights into discrete selections
    with controlled error. -/
axiom barany_grinberg (v : ι → (Fin d → ℝ)) (hv : ∀ i j, |v i j| ≤ 1)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 0 ∨ ε i = 1) ∧
      ∀ j, |∑ i, (ε i - a i) * v i j| ≤ d
