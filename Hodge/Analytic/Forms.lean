import Hodge.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

instance smoothFormZero (k : ℕ) : Zero (SmoothForm n X k) where
  zero := ⟨fun _ => 0⟩

instance smoothFormAdd (k : ℕ) : Add (SmoothForm n X k) where
  add := fun α β => ⟨fun x => α.as_alternating x + β.as_alternating x⟩

instance smoothFormNeg (k : ℕ) : Neg (SmoothForm n X k) where
  neg := fun α => ⟨fun x => -α.as_alternating x⟩

instance smoothFormSMul (k : ℕ) : SMul ℝ (SmoothForm n X k) where
  smul := fun r α => ⟨fun x => (r : ℂ) • α.as_alternating x⟩

instance smoothFormSub (k : ℕ) : Sub (SmoothForm n X k) where
  sub := fun α β => ⟨fun x => α.as_alternating x - β.as_alternating x⟩

instance smoothFormAddCommGroup (k : ℕ) : AddCommGroup (SmoothForm n X k) where
  add_assoc := fun _ _ _ => sorry
  zero_add := fun _ => sorry
  add_zero := fun _ => sorry
  neg_add_cancel := fun _ => sorry
  add_comm := fun _ _ => sorry
  sub_eq_add_neg := fun _ _ => sorry
  nsmul := fun m α => ⟨fun x => m • α.as_alternating x⟩
  nsmul_zero := fun _ => sorry
  nsmul_succ := fun _ _ => sorry
  zsmul := fun z α => ⟨fun x => z • α.as_alternating x⟩
  zsmul_zero' := fun _ => sorry
  zsmul_succ' := fun _ _ => sorry
  zsmul_neg' := fun _ _ => sorry

instance smoothFormModule (k : ℕ) : Module ℝ (SmoothForm n X k) where
  one_smul := fun _ => sorry
  mul_smul := fun _ _ _ => sorry
  smul_zero := fun _ => sorry
  smul_add := fun _ _ _ => sorry
  add_smul := fun _ _ _ => sorry
  zero_smul := fun _ => sorry

variable [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

def kahlerForm : SmoothForm n X 2 := K.omega_form

def extDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k + 1) := ⟨fun _ => sorry⟩

theorem d_squared_zero {k : ℕ} (ω : SmoothForm n X k) : extDeriv (extDeriv ω) = 0 := sorry

def wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) : SmoothForm n X (k + l) := ⟨fun _ => sorry⟩

def hodgeStar {k : ℕ} (α : SmoothForm n X k) : SmoothForm n X (2 * n - k) := ⟨fun _ => sorry⟩

def adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1) := sorry

def laplacian {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k := sorry

def lefschetzL {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k + 2) := ⟨fun _ => sorry⟩

def lefschetzLambda {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k - 2) := sorry

def gradingH {k : ℕ} (α : SmoothForm n X k) : SmoothForm n X k := ((k : ℝ) - (n : ℝ)) • α

def isHarmonic {k : ℕ} (ω : SmoothForm n X k) : Prop := laplacian ω = 0

def isClosed {k : ℕ} (ω : SmoothForm n X k) : Prop := extDeriv ω = 0

def isPrimitive {k : ℕ} (η : SmoothForm n X k) : Prop := lefschetzLambda η = 0

end
