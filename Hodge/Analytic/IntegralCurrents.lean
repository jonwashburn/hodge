import Hodge.Analytic.Currents
import Hodge.Analytic.FlatNorm
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Track B.4: Integral Currents

This file defines integral currents on Kähler manifolds.
Since Current operations are opaque, most properties are axiomatized.
-/

noncomputable section

open Classical MeasureTheory

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]

/-- **Rectifiability** (Federer, 1969).
    A set S ⊆ X is k-rectifiable if it can be covered (up to measure zero)
    by countably many Lipschitz images of subsets of ℝ^k.
    Reference: [H. Federer, "Geometric Measure Theory", 1969, Section 3.2]. -/
opaque isRectifiable (k : ℕ) (S : Set X) : Prop

axiom isRectifiable_empty (k : ℕ) : isRectifiable k (∅ : Set X)
axiom isRectifiable_union (k : ℕ) (S₁ S₂ : Set X) :
    isRectifiable k S₁ → isRectifiable k S₂ → isRectifiable k (S₁ ∪ S₂)

/-- **Integral Polyhedral Chains**
    The set of currents that are finite sums of oriented simplices
    with integer multiplicities. -/
opaque IntegralPolyhedralChain (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] : Set (Current n X k)

axiom polyhedral_add {k : ℕ} (S T : Current n X k) :
    S ∈ IntegralPolyhedralChain n X k → T ∈ IntegralPolyhedralChain n X k → S + T ∈ IntegralPolyhedralChain n X k
axiom polyhedral_zero {k : ℕ} : (0 : Current n X k) ∈ IntegralPolyhedralChain n X k
axiom polyhedral_smul {k : ℕ} (c : ℤ) (T : Current n X k) :
    T ∈ IntegralPolyhedralChain n X k → (c • T) ∈ IntegralPolyhedralChain n X k
axiom polyhedral_boundary {k : ℕ} (T : Current n X (k + 1)) :
    T ∈ IntegralPolyhedralChain n X (k + 1) → Current.boundary T ∈ IntegralPolyhedralChain n X k

/-- Predicate stating that a current is an integral current.
    Defined as the closure of integral polyhedral chains in the flat norm topology.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
def isIntegral {k : ℕ} (T : Current n X k) : Prop :=
  ∀ ε > 0, ∃ P ∈ IntegralPolyhedralChain n X k, flatNorm (T - P) < ε

/-- **Theorem: Sum of Integral Currents is Integral** (Federer-Fleming, 1960). -/
axiom isIntegral_add {k : ℕ} (S T : Current n X k) :
    isIntegral S → isIntegral T → isIntegral (S + T)

/-- **Theorem: Zero current is integral.** -/
theorem isIntegral_zero_current (k : ℕ) : isIntegral (0 : Current n X k) := by
  intro ε hε
  use 0, polyhedral_zero
  have h : (0 : Current n X k) - 0 = 0 := by
    show (0 : Current n X k) + -(0 : Current n X k) = 0
    rw [Current.neg_zero_current, Current.add_zero]
  rw [h, flatNorm_zero]
  exact hε

/-- **Theorem: Integer Scaling of Integral Currents is Integral.** -/
axiom isIntegral_smul {k : ℕ} (c : ℤ) (T : Current n X k) :
    isIntegral T → isIntegral (c • T)

/-- **The boundary of an integral current is integral.** -/
axiom isIntegral_boundary {k : ℕ} (T : Current n X (k + 1)) :
    isIntegral T → isIntegral (Current.boundary T)

/-- An integral current structure wrapping the predicate. -/
structure IntegralCurrent (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  toFun : Current n X k
  is_integral : isIntegral toFun

/-- The zero integral current. -/
def zero_int (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] :
    IntegralCurrent n X k :=
  { toFun := 0
    is_integral := isIntegral_zero_current k }

instance {k : ℕ} : Inhabited (IntegralCurrent n X k) :=
  ⟨zero_int n X k⟩

/-- Convert an IntegralCurrent to a Current. -/
instance {k : ℕ} : Coe (IntegralCurrent n X k) (Current n X k) where
  coe := IntegralCurrent.toFun

/-- The isCycle property for IntegralCurrent. -/
def IntegralCurrent.isCycleAt {k : ℕ} (T : IntegralCurrent n X k) : Prop :=
  ∃ (k' : ℕ) (h : k = k' + 1), (Current.boundary (h ▸ T.toFun)) = 0

/-- Boundary of an integral current. -/
def IntegralCurrent.boundary {k : ℕ} (T : IntegralCurrent n X (k + 1)) :
    IntegralCurrent n X k where
  toFun := Current.boundary T.toFun
  is_integral := isIntegral_boundary T.toFun T.is_integral

/-- If an integral current is a cycle, its boundary mass is zero. -/
theorem IntegralCurrent.boundary_mass_zero {k : ℕ} (T : IntegralCurrent n X (k + 1))
    (h_cycle : T.isCycleAt) : Current.mass (Current.boundary T.toFun) = 0 := by
  obtain ⟨k', h_dim, h_bdy⟩ := h_cycle
  cases h_dim
  simp only at h_bdy
  rw [h_bdy]
  exact Current.mass_zero

end
