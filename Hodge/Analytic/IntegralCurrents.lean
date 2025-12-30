import Hodge.Analytic.Currents
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Track B.4: Integral Currents
-/

noncomputable section

open Classical MeasureTheory

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X]

/-- **Rectifiability** (Federer, 1969).
    A set S ⊆ X is k-rectifiable if it is the image of a bounded subset of ℝ^k under
    a Lipschitz map.
    Reference: [H. Federer, "Geometric Measure Theory", 1969, Section 3.2]. -/
opaque isRectifiable (k : ℕ) (S : Set X) : Prop

axiom isRectifiable_empty (k : ℕ) : isRectifiable k (∅ : Set X)
axiom isRectifiable_union (k : ℕ) (S₁ S₂ : Set X) :
    isRectifiable k S₁ → isRectifiable k S₂ → isRectifiable k (S₁ ∪ S₂)

/-- Predicate stating that a current is represented by integration over
    a rectifiable set with integer multiplicity.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
opaque isIntegral {k : ℕ} (T : Current n X k) : Prop

/-- **Theorem: Sum of Integral Currents is Integral** (Federer-Fleming, 1960). -/
axiom isIntegral_add {k : ℕ} (S T : Current n X k) :
    isIntegral S → isIntegral T → isIntegral (S + T)

/-- **Theorem: Zero current is integral.** -/
axiom isIntegral_zero_current (k : ℕ) [Nonempty X] : isIntegral (0 : Current n X k)

/-- **Theorem: Integer Scaling of Integral Currents is Integral.** -/
axiom isIntegral_smul {k : ℕ} (c : ℤ) (T : Current n X k) :
    isIntegral T → isIntegral (c • T)

/-- **The boundary of an integral current is integral.** -/
axiom isIntegral_boundary {k : ℕ} (T : Current n X (k + 1)) :
    isIntegral T → isIntegral T.boundary

/-- An integral current structure wrapping the predicate. -/
structure IntegralCurrent (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  toFun : Current n X k
  is_integral : isIntegral toFun

/-- The zero integral current (axiomatized as integral via `isIntegral_zero_current`). -/
def IntegralCurrent.zero (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] :
    IntegralCurrent n X k :=
  { toFun := 0
    is_integral := isIntegral_zero_current k }

instance {k : ℕ} : Inhabited (IntegralCurrent n X k) :=
  ⟨IntegralCurrent.zero n X k⟩

/-- Convert an IntegralCurrent to a Current. -/
instance {k : ℕ} : Coe (IntegralCurrent n X k) (Current n X k) where
  coe := IntegralCurrent.toFun

/-- The isCycle property for IntegralCurrent. -/
def IntegralCurrent.isCycleAt {k : ℕ} (T : IntegralCurrent n X k) : Prop :=
  ∃ (k' : ℕ) (h : k = k' + 1), (h ▸ T.toFun).boundary = 0

def IntegralCurrent.boundary {k : ℕ} (T : IntegralCurrent n X (k + 1)) :
    IntegralCurrent n X k where
  toFun := T.toFun.boundary
  is_integral := isIntegral_boundary T.toFun T.is_integral

end
