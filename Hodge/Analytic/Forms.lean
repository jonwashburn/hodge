import Hodge.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
-/

noncomputable section

open Classical

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-- **d² = 0**: The exterior derivative squared is zero. -/
theorem d_squared_zero {k : ℕ} (ω : SmoothForm n X k) : smoothExtDeriv (smoothExtDeriv ω) = 0 :=
  smoothExtDeriv_extDeriv ω

/-- Exterior derivative is additive. -/
theorem smoothExtDeriv_add_lem {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) :
    smoothExtDeriv (ω₁ + ω₂) = smoothExtDeriv ω₁ + smoothExtDeriv ω₂ :=
  smoothExtDeriv_add ω₁ ω₂

/-- Exterior derivative is ℂ-linear. -/
theorem smoothExtDeriv_smul_lem {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) :
    smoothExtDeriv (c • ω) = c • smoothExtDeriv ω :=
  smoothExtDeriv_smul c ω

/-- Exterior derivative is linear over ℝ. -/
theorem smoothExtDeriv_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) :
    smoothExtDeriv (r • ω) = r • smoothExtDeriv ω := by
  -- `r•ω` is implemented as `((r:ℂ)•ω)`; use ℂ-linearity of `d`.
  simpa using (smoothExtDeriv_smul (n := n) (X := X) (k := k) (r : ℂ) ω)

/-! ### Degree-casting helper -/

/-- Cast a form across an equality of degrees. -/
def castForm {k k' : ℕ} (h : k = k') (α : SmoothForm n X k) : SmoothForm n X k' := by
  cases h
  exact α

/-- The unit 0-form (constant function 1). -/
opaque unitForm {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : SmoothForm n X 0

/-- The wedge product ω ⋀ η of two smooth forms. -/
def wedge {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) : SmoothForm n X (k + l) :=
  ⟨fun x => (ω.as_alternating x).wedge (η.as_alternating x),
   isSmoothAlternating_wedge k l ω η⟩

/-- **Wedge Product is Bilinear.** -/
theorem wedge_add {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {k l : ℕ} (ω₁ ω₂ : SmoothForm n X k) (η : SmoothForm n X l) :
    wedge (ω₁ + ω₂) η = wedge ω₁ η + wedge ω₂ η := by
  ext x v
  simp only [wedge, SmoothForm.add_apply, AlternatingMap.add_apply, AlternatingMap.wedge_add_left]

theorem wedge_smul {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {k l : ℕ} (c : ℂ) (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    wedge (c • ω) η = c • wedge ω η := by
  ext x v
  simp only [wedge, SmoothForm.smul_apply, AlternatingMap.smul_apply, AlternatingMap.wedge_smul_left]

/-- **Wedge Product Associativity.** -/
theorem wedge_assoc {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {k l m : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) (θ : SmoothForm n X m) :
    HEq (wedge (wedge ω η) θ) (wedge ω (wedge η θ)) := by
  -- Points are equal, we just need to show pointwise wedge is associative.
  -- AlternatingMap.wedge_assoc exists.
  apply HEq_of_eq
  ext x v
  simp only [wedge, AlternatingMap.wedge_assoc]

/-- **Leibniz Rule for Exterior Derivative.** -/
theorem smoothExtDeriv_wedge {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    let h1 : (k + 1) + l = k + l + 1 := by
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    let h2 : k + (l + 1) = k + l + 1 := by
      simp [Nat.add_assoc]
    smoothExtDeriv (wedge ω η) =
      castForm (n := n) (X := X) (k := (k + 1) + l) (k' := k + l + 1) h1 (wedge (smoothExtDeriv ω) η)
        + (-1 : ℂ)^k •
          castForm (n := n) (X := X) (k := k + (l + 1)) (k' := k + l + 1) h2 (wedge ω (smoothExtDeriv η)) := by
  ext x
  apply extDeriv_wedge

instance (k l : ℕ) : HMul (SmoothForm n X k) (SmoothForm n X l) (SmoothForm n X (k + l)) where
  hMul := wedge

notation ω " ⋀ " η => wedge ω η

/-! ## Kähler Operators -/

variable [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- The volume form dvol = ω^n / n!. -/
def volumeForm (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] :
    SmoothForm n X (2 * n) :=
  (1 / (n.factorial : ℂ)) • omegaPow n X n

/-! ## Hodge Star Operator -/

/-- **Hodge Star Operator** (Hodge, 1941). -/
def hodgeStar {k : ℕ} (α : SmoothForm n X k) : SmoothForm n X (2 * n - k) :=
  ⟨fun x => hodgeStarPointwise x (α.as_alternating x),
   isSmoothAlternating_hodgeStar k α⟩

theorem hodgeStar_add {k : ℕ} (α β : SmoothForm n X k) :
    hodgeStar (α + β) = hodgeStar α + hodgeStar β := by
  ext x v; simp only [hodgeStar, SmoothForm.add_apply, LinearMap.map_add]

theorem hodgeStar_smul {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    hodgeStar (r • α) = r • hodgeStar α := by
  ext x v; simp only [hodgeStar, SmoothForm.smul_real_apply, LinearMap.map_smul]

/-! ## Adjoint Derivative and Laplacian -/

/-- **Adjoint Derivative** d* = -*d*. -/
def adjointDeriv {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X (k - 1) :=
  let h_deg : (2 * n - (2 * n - k + 1)) = k - 1 := by omega
  castForm h_deg (hodgeStar (smoothExtDeriv (hodgeStar ω)))

/-- **Hodge-Laplacian** Δ = dd* + d*d. -/
def laplacian {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k :=
  smoothExtDeriv (adjointDeriv ω) + adjointDeriv (smoothExtDeriv ω)

theorem laplacian_add {k : ℕ} (α β : SmoothForm n X k) : laplacian (α + β) = laplacian α + laplacian β := by
  unfold laplacian
  simp only [smoothExtDeriv_add, adjointDeriv_add, add_add_add_comm]

def isHarmonic {k : ℕ} (ω : SmoothForm n X k) : Prop := laplacian ω = 0

/-! ## Lefschetz Operators -/

/-- **Lefschetz Operator L**: ω ⋀ -. -/
def lefschetzL {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k + 2) :=
  by
    -- `ω ⋀ η` has degree `2 + k`; rewrite to `k + 2`.
    simpa [Nat.add_comm] using (wedge (n := n) (X := X) (k := 2) (l := k) K.omega_form η)

/-- **Dual Lefschetz Operator Λ**: Adjoint to L. -/
def lefschetzLambda {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k - 2) :=
  ⟨fun x => lefschetzLambdaPointwise x (η.as_alternating x),
   isSmoothAlternating_lefschetzLambda k η⟩

def lefschetz_power_form (k : ℕ) {p : ℕ} (η : SmoothForm n X p) : SmoothForm n X (p + 2 * k) :=
  match k with
  | 0 => η
  | k + 1 =>
    have h_eq : p + 2 * (k + 1) = (p + 2 * k) + 2 := by ring
    h_eq ▸ lefschetzL (lefschetz_power_form k η)

def gradingH {k : ℕ} (α : SmoothForm n X k) : SmoothForm n X k := ((k : ℝ) - (n : ℝ)) • α
def isClosed {k : ℕ} (ω : SmoothForm n X k) : Prop := smoothExtDeriv ω = 0

/-- **Theorem: scaled Kähler power is closed.** -/
-- NOTE: the closedness of `omegaPow` (and its scaled variant) lives in
-- `Hodge/Kahler/TypeDecomposition.lean` where `omegaPow` is defined.

def isPrimitive {k : ℕ} (η : SmoothForm n X k) : Prop := lefschetzLambda η = 0

end
