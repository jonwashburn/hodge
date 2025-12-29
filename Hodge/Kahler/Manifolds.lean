import Hodge.Basic
import Hodge.Analytic.Currents
import Hodge.Analytic.IntegralCurrents
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Track C.1: Kähler Manifolds
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

/-- The wedge product of two rational forms is rational. -/
axiom isRationalClass_wedge {k l : ℕ} {ω₁ : SmoothForm n X k} {ω₂ : SmoothForm n X l} :
    isRationalClass (DeRhamCohomologyClass.ofForm ω₁) →
    isRationalClass (DeRhamCohomologyClass.ofForm ω₂) →
    isRationalClass (DeRhamCohomologyClass.ofForm (wedge ω₁ ω₂))

/-- Scalar multiplication by a rational number preserves rationality (on forms). -/
axiom isRationalClass_smul_rat {k : ℕ} (q : ℚ) {ω : SmoothForm n X k} :
    isRationalClass (DeRhamCohomologyClass.ofForm ω) →
    isRationalClass (DeRhamCohomologyClass.ofForm ((q : ℝ) • ω))

/-- The Kähler form represents a rational cohomology class. -/
axiom omega_is_rational : isRationalClass (DeRhamCohomologyClass.ofForm K.omega_form)

/-- Addition of rational classes is rational (on forms). -/
axiom isRationalClass_add {k : ℕ} {ω₁ ω₂ : SmoothForm n X k} :
    isRationalClass (DeRhamCohomologyClass.ofForm ω₁) →
    isRationalClass (DeRhamCohomologyClass.ofForm ω₂) →
    isRationalClass (DeRhamCohomologyClass.ofForm (ω₁ + ω₂))

/-- The zero class is rational. -/
axiom zero_is_rational {k : ℕ} : isRationalClass (DeRhamCohomologyClass.ofForm (0 : SmoothForm n X k))

/-- The unit form represents a rational cohomology class. -/
axiom unitForm_is_rational : isRationalClass (DeRhamCohomologyClass.ofForm (unitForm (n := n) (X := X)))

end
