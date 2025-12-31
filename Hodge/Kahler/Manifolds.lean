import Hodge.Basic
import Hodge.Analytic.Currents
import Hodge.Analytic.IntegralCurrents
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.Alternating.Basic

/-!
-/

noncomputable section

open Classical

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- **Kähler Metric Symmetry** (Kobayashi, 1987).
    The Riemannian metric induced by the Kähler form is symmetric.
    Reference: [S. Kobayashi, "Differential Geometry of Complex Vector Bundles",
    Princeton University Press, 1987, Chapter II, Section 3]. -/
axiom kahlerMetric_symm (x : X) (v w : TangentSpace (𝓒_complex n) x) :
    (K.omega_form.as_alternating x ![v, Complex.I • w]).re =
    (K.omega_form.as_alternating x ![w, Complex.I • v]).re

/-! ## Rationality -/

/-- The wedge product of two rational cohomology classes is rational. -/
axiom isRationalClass_wedge {k l : ℕ}
    (η₁ : DeRhamCohomologyClass n X k) (η₂ : DeRhamCohomologyClass n X l) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂)

-- isRationalClass_smul_rat is defined in Basic.lean

/-- **Axiom: Kähler form is closed (dω = 0).** -/
axiom omega_isClosed : IsFormClosed (K.omega_form)

/-- The Kähler form represents a rational cohomology class. -/
axiom omega_is_rational : isRationalClass ⟦K.omega_form, omega_isClosed⟧

-- isRationalClass_add is defined in Basic.lean

/-- The zero class is rational. -/
axiom zero_is_rational {k : ℕ} : isRationalClass (0 : DeRhamCohomologyClass n X k)

/-- **Axiom: Unit form is closed.** -/
axiom unitForm_isClosed : IsFormClosed (unitForm : SmoothForm n X 0)

/-- The unit form represents a rational cohomology class. -/
axiom unitForm_is_rational : isRationalClass ⟦(unitForm : SmoothForm n X 0), unitForm_isClosed⟧

end

