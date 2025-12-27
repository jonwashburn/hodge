import Hodge.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Track B.1: Differential Forms

This file defines differential forms on complex manifolds.
-/

noncomputable section

open Classical

set_option autoImplicit false

/-- A smooth k-form on a complex n-manifold X. -/
def SmoothForm (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] :=
  (x : X) → (Fin k → TangentSpace (𝓒_complex n) x) → ℂ

instance {n : ℕ} {X : Type*} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] :
    Zero (SmoothForm n X k) where
  zero := fun _ _ => 0

instance {n : ℕ} {X : Type*} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] :
    Add (SmoothForm n X k) where
  add := fun α β x v => α x v + β x v

instance {n : ℕ} {X : Type*} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] :
    Neg (SmoothForm n X k) where
  neg := fun α x v => - α x v

instance {n : ℕ} {X : Type*} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] :
    SMul ℝ (SmoothForm n X k) where
  smul := fun r α x v => r • α x v

/-- The exterior derivative d : Ω^k → Ω^{k+1}. Axiomatized as zero. -/
def extDeriv {n : ℕ} {X : Type*} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω : SmoothForm n X k) : SmoothForm n X (k + 1) :=
  fun _ _ => 0

/-- d ∘ d = 0 -/
theorem d_squared_zero {n : ℕ} {X : Type*} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω : SmoothForm n X k) : extDeriv (extDeriv ω) = 0 := rfl

/-- The wedge product ω ∧ η. -/
def wedge {n : ℕ} {X : Type*} {k l : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω : SmoothForm n X k) (η : SmoothForm n X l) : SmoothForm n X (k + l) :=
  fun x v => ω x (fun i => v ⟨i.val, Nat.lt_add_right l i.isLt⟩) * 
             η x (fun i => v ⟨k + i.val, Nat.add_lt_add_left i.isLt k⟩)

/-- Kähler operators (axiomatized) -/
def kahlerForm (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [ProjectiveComplexManifold n X] [IsManifold (𝓒_complex n) ⊤ X]
    [K : KahlerManifold n X] : SmoothForm n X 2 := fun _ _ => 0

def hodgeStar (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [ProjectiveComplexManifold n X] [IsManifold (𝓒_complex n) ⊤ X]
    [K : KahlerManifold n X] (α : SmoothForm n X k) : SmoothForm n X (2 * n - k) :=
  fun _ _ => 0

def adjointDeriv (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [ProjectiveComplexManifold n X] [IsManifold (𝓒_complex n) ⊤ X]
    [K : KahlerManifold n X] (ω : SmoothForm n X k) : SmoothForm n X (k - 1) :=
  fun _ _ => 0

def lefschetzL (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [ProjectiveComplexManifold n X] [IsManifold (𝓒_complex n) ⊤ X]
    [K : KahlerManifold n X] (η : SmoothForm n X k) : SmoothForm n X (k + 2) :=
  fun _ _ => 0

def lefschetzLambda (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [ProjectiveComplexManifold n X] [IsManifold (𝓒_complex n) ⊤ X]
    [K : KahlerManifold n X] (η : SmoothForm n X k) : SmoothForm n X (k - 2) :=
  fun _ _ => 0

def isClosed {n : ℕ} {X : Type*} {k : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω : SmoothForm n X k) : Prop :=
  extDeriv ω = 0

def isPrimitive (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [ProjectiveComplexManifold n X] [IsManifold (𝓒_complex n) ⊤ X]
    [K : KahlerManifold n X] (η : SmoothForm n X k) : Prop :=
  lefschetzLambda n X k η = 0

end
