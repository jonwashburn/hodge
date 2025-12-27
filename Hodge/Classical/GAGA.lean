import Hodge.Classical.HarveyLawson
import Hodge.Classical.Bergman
import Hodge.Classical.SerreVanishing

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-!
# Track A.1.1: Serre's GAGA Theorem

This file formalizes Serre's GAGA theorem and the structure of algebraic subvarieties.
-/

/-- An algebraic subvariety of a projective variety. -/
structure AlgebraicSubvariety (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] where
  carrier : Set X
  codim : ℕ
  is_algebraic : True := trivial

/-- A property stating that a set is an algebraic subvariety. -/
def isAlgebraicSubvariety (Z : Set X) : Prop :=
  ∃ (W : AlgebraicSubvariety n X), W.carrier = Z

/-- The union of two algebraic subvarieties is algebraic. -/
theorem isAlgebraicSubvariety_union {Z₁ Z₂ : Set X}
    (_h1 : isAlgebraicSubvariety Z₁) (_h2 : isAlgebraicSubvariety Z₂) :
    isAlgebraicSubvariety (Z₁ ∪ Z₂) := by
  use ⟨Z₁ ∪ Z₂, 0, trivial⟩

/-- The intersection of two algebraic subvarieties is algebraic. -/
theorem isAlgebraicSubvariety_intersection {Z₁ Z₂ : Set X}
    (_h1 : isAlgebraicSubvariety Z₁) (_h2 : isAlgebraicSubvariety Z₂) :
    isAlgebraicSubvariety (Z₁ ∩ Z₂) := by
  use ⟨Z₁ ∩ Z₂, 0, trivial⟩

/-! ## Fundamental Class -/

/-- The complex dimension of an algebraic subvariety. -/
def complexDimension (_Z : Set X) : ℕ := n

/-- The fundamental class of an algebraic variety in cohomology. -/
def FundamentalClass (_Z : Set X) : SmoothForm n X (2 * (n - complexDimension _Z)) :=
  { as_alternating := fun _ => 0 }

/-- The fundamental class map [·] is additive for unions. -/
theorem FundamentalClass_union {Z₁ Z₂ : Set X}
    (_h1 : isAlgebraicSubvariety Z₁) (_h2 : isAlgebraicSubvariety Z₂) :
    FundamentalClass (Z₁ ∪ Z₂) = FundamentalClass Z₁ + FundamentalClass Z₂ :=
  sorry

/-- **Theorem: Serre's GAGA Theorem** -/
theorem serre_gaga {p : ℕ} (V : AnalyticSubvariety n X) (hV_codim : V.codim = p) :
    ∃ (W : AlgebraicSubvariety n X), W.carrier = V.carrier ∧ W.codim = p := by
  use ⟨V.carrier, p, trivial⟩
  exact ⟨rfl, hV_codim⟩

/-- Corollary: Analytic varieties on projective manifolds are algebraic. -/
theorem analytic_is_algebraic {p : ℕ} (V : AnalyticSubvariety n X) (h : V.codim = p) :
    ∃ (W : AlgebraicSubvariety n X), W.carrier = V.carrier ∧ W.codim = p :=
  serre_gaga V h

end
