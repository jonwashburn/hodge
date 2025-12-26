import Hodge.Classical.HarveyLawson
import Hodge.Classical.Bergman
import Hodge.Classical.SerreVanishing

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-!
# Track A.1.1: Serre's GAGA Theorem

This file formalizes Serre's GAGA (Géométrie Algébrique et Géométrie Analytique) theorem.

## Mathematical Statement
Every complex analytic subvariety of a projective variety is algebraic.

## Reference
[Serre, "Géométrie algébrique et géométrie analytique", Ann. Inst. Fourier 1956]
-/

/-- An algebraic subvariety of a projective variety.
Defined as the common zero set of finitely many global sections of an ample line bundle. -/
structure AlgebraicSubvariety (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
    [ProjectiveComplexManifold n X] where
  /-- The underlying set -/
  carrier : Set X
  /-- Codimension of the variety -/
  codim : ℕ
  /-- Algebraicity: defined by vanishing of sections of some L^M -/
  exists_sections : ∃ (L : HolomorphicLineBundle n X) [hL : IsAmple L] (M : ℕ)
    (s : Finset (BergmanSpace L M)),
    carrier = ⋂ s_i ∈ s, s_i.zero_set

/-- **Theorem: Serre's GAGA Theorem**

Every complex analytic subvariety of a projective variety is algebraic.

Reference: [Serre, 1956]. -/
theorem serre_gaga {p : ℕ} (V : AnalyticSubvariety n X) (hV_codim : V.codim = p) :
    ∃ (W : AlgebraicSubvariety n X), W.carrier = V.carrier ∧ W.codim = p :=
  sorry

/-- Corollary: Analytic varieties on projective manifolds are algebraic. -/
theorem analytic_is_algebraic {p : ℕ} (V : AnalyticSubvariety n X) (h : V.codim = p) :
    ∃ (W : AlgebraicSubvariety n X), W.carrier = V.carrier ∧ W.codim = p :=
  serre_gaga V h
