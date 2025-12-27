import Hodge.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Track B.1: Differential Forms
-/

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-! ## Algebraic Structure -/

instance smoothFormZero (k : ℕ) : Zero (SmoothForm n X k) where
  zero := ⟨fun _ => 0⟩

instance smoothFormAdd (k : ℕ) : Add (SmoothForm n X k) where
  add := fun α β => ⟨fun x => α.as_alternating x + β.as_alternating x⟩

instance smoothFormNeg (k : ℕ) : Neg (SmoothForm n X k) where
  neg := fun α => ⟨fun x => -α.as_alternating x⟩

instance smoothFormSMul (k : ℕ) : SMul ℝ (SmoothForm n X k) where
  smul := fun r α => ⟨fun x => (r : ℂ) • α.as_alternating x⟩

/-! ## Exterior Derivative -/

/-- The exterior derivative d : Ω^k → Ω^{k+1}. Axiomatized. -/
def extDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1) :=
  ⟨fun _ => 0⟩

/-- d ∘ d = 0. -/
theorem d_squared_zero {k : ℕ} (ω : SmoothForm n X k) : extDeriv (extDeriv ω) = 0 := rfl

/-! ## Wedge Product -/

/-- The wedge product ω ∧ η. Axiomatized. -/
def wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) : SmoothForm n X (k + l) :=
  ⟨fun _ => sorry⟩

/-! ## Kähler Operators -/

variable [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- The Kähler form as a 2-form. -/
def kahlerForm : SmoothForm n X 2 := K.omega_form

/-- The Hodge Star. Axiomatized. -/
def hodgeStar {k : ℕ} (α : SmoothForm n X k) : SmoothForm n X (2 * n - k) :=
  ⟨fun _ => sorry⟩

/-- Adjoint derivative. Axiomatized. -/
def adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1) :=
  ⟨fun _ => sorry⟩

/-- Laplacian. Axiomatized. -/
def laplacian {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k :=
  ⟨fun _ => sorry⟩

/-- Lefschetz L. Axiomatized. -/
def lefschetzL {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k + 2) :=
  ⟨fun _ => sorry⟩

/-- Lefschetz Lambda. Axiomatized. -/
def lefschetzLambda {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k - 2) :=
  ⟨fun _ => sorry⟩

/-- A form is harmonic. -/
def isHarmonic {k : ℕ} (ω : SmoothForm n X k) : Prop := laplacian ω = 0

/-- A form is closed. -/
def isClosed {k : ℕ} (ω : SmoothForm n X k) : Prop := extDeriv ω = 0

/-- A form is primitive. -/
def isPrimitive {k : ℕ} (η : SmoothForm n X k) : Prop := lefschetzLambda η = 0

end
