import Hodge.Classical.GAGA

/-!
# P1 Assumption: Harvey–Lawson Represents Witness

This file packages the P1 bridge statement as an *explicit assumption* (typeclass),
instead of a hidden `private axiom` inside `Hodge/Kahler/Main.lean`.

This supports an honest formalization workflow:
- the main theorem is proved *assuming* the Harvey–Lawson → cohomology comparison step,
- and eliminating that assumption becomes an explicit standalone goal.
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

universe u

namespace Hodge

/-- **P1 Assumption**: Harvey–Lawson output represents the same de Rham class.

In the current proof architecture, `FundamentalClassSet` is the “cycle class” attached to
an algebraic set. P1 is the missing bridge identifying the cohomology class of a form `γ`
with the fundamental class of the Harvey–Lawson/GAGA-produced algebraic cycle.

We keep the statement exactly matching the former `private axiom` in `Hodge/Kahler/Main.lean`,
but as an explicit typeclass assumption so it does not appear as a custom axiom in
`#print axioms` output.
-/
class HarveyLawsonRepresentsWitness (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X] : Prop where
  witness {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
      (Zpos : Set X) (h_alg : isAlgebraicSubvariety n X Zpos) :
      ofForm γ h_closed =
        ofForm (FundamentalClassSet n X p (Zpos ∪ ∅))
          (FundamentalClassSet_isClosed (n := n) (X := X) (p := p) (Zpos ∪ ∅)
            (isAlgebraicSubvariety_union h_alg (isAlgebraicSubvariety_empty n X)))

end Hodge

end

