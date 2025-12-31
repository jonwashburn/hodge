import Hodge.Basic
import Hodge.Kahler.Main

/-!
# The Hodge Conjecture (Final Formalization)

This is the top-level entry point for the Hodge Conjecture formalization.
The full proof logic is contained in `Hodge/Kahler/Main.lean`.
-/

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-- **The Hodge Conjecture** (Hodge, 1950; Millennium Prize Problem).
    For a smooth projective complex algebraic variety X, every rational Hodge class
    is algebraic (i.e., it is represented by a signed algebraic cycle). -/
theorem hodge_conjecture {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_rational : isRationalClass (DeRhamCohomologyClass.ofForm γ h_closed)) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : SignedAlgebraicCycle n X), Z.RepresentsClass (DeRhamCohomologyClass.ofForm γ h_closed) :=
  hodge_conjecture' γ h_closed h_rational h_p_p

end
