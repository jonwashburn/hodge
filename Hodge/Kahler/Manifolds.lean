import Hodge.Basic
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

/-- The wedge product of two rational cohomology classes is rational.
    This follows directly from isRationalClass_mul in Basic.lean. -/
theorem isRationalClass_wedge {k l : ℕ}
    (η₁ : DeRhamCohomologyClass n X k) (η₂ : DeRhamCohomologyClass n X l) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂) :=
  isRationalClass_mul η₁ η₂

-- isRationalClass_smul_rat is defined in Basic.lean

/-- The Kähler form is closed (dω = 0).
    This follows directly from the KahlerManifold class axiom K.omega_closed. -/
theorem omega_isClosed : IsFormClosed (K.omega_form) :=
  K.omega_closed

/-- The Kähler form represents a rational cohomology class. -/
axiom omega_is_rational : isRationalClass ⟦K.omega_form, omega_isClosed⟧

-- isRationalClass_add is defined in Basic.lean

/-- The zero class is rational.
    This follows directly from isRationalClass_zero in Basic.lean. -/
theorem zero_is_rational {k : ℕ} : isRationalClass (0 : DeRhamCohomologyClass n X k) :=
  isRationalClass_zero

/-- Negation of a rational class is rational.
    Directly uses isRationalClass_neg from Basic.lean. -/
theorem neg_is_rational {k : ℕ} (η : DeRhamCohomologyClass n X k)
    (h : isRationalClass η) : isRationalClass (-η) :=
  isRationalClass_neg η h

/-- Difference of rational classes is rational.
    Directly uses isRationalClass_sub from Basic.lean. -/
theorem sub_is_rational {k : ℕ} (η₁ η₂ : DeRhamCohomologyClass n X k)
    (h₁ : isRationalClass η₁) (h₂ : isRationalClass η₂) :
    isRationalClass (η₁ - η₂) :=
  isRationalClass_sub η₁ η₂ h₁ h₂

/-- Sum of rational classes is rational.
    Directly uses isRationalClass_add from Basic.lean. -/
theorem add_is_rational {k : ℕ} (η₁ η₂ : DeRhamCohomologyClass n X k)
    (h₁ : isRationalClass η₁) (h₂ : isRationalClass η₂) :
    isRationalClass (η₁ + η₂) :=
  isRationalClass_add η₁ η₂ h₁ h₂

/-- **Axiom: Unit form is closed.** -/
axiom unitForm_isClosed : IsFormClosed (unitForm : SmoothForm n X 0)

/-- The unit form represents a rational cohomology class. -/
axiom unitForm_is_rational : isRationalClass ⟦(unitForm : SmoothForm n X 0), unitForm_isClosed⟧

end
