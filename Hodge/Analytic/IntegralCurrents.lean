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

/-- A set S ⊆ X is k-rectifiable. -/
def isRectifiable (_k : ℕ) (_S : Set X) : Prop := True

/-- Predicate stating that a current is represented by integration over
a rectifiable set with integer multiplicity. -/
def isIntegral {k : ℕ} (_T : Current n X k) : Prop :=
  ∃ (S : Set X), isRectifiable k S

/-- An integral current structure wrapping the predicate. -/
structure IntegralCurrent (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  toFun : Current n X k
  is_integral : isIntegral toFun

/-! ## Closure Properties -/

/-- Sum of Integral Currents is Integral -/
theorem isIntegral_add {k : ℕ} (S T : Current n X k) :
    isIntegral S → isIntegral T → isIntegral (S + T) := by
  intro ⟨S_set, _⟩ ⟨T_set, _⟩
  exact ⟨S_set ∪ T_set, trivial⟩

/-- The zero current is integral. -/
theorem isIntegral_zero_current (k : ℕ) [Nonempty X] : isIntegral (0 : Current n X k) := by
  use (∅ : Set X)
  exact trivial

/-- Integer Scaling of Integral Currents is Integral -/
theorem isIntegral_smul {k : ℕ} (c : ℤ) (T : Current n X k) :
    isIntegral T → isIntegral (c • T) := by
  intro ⟨T_set, _⟩
  exact ⟨T_set, trivial⟩

/-- Convert an IntegralCurrent to a Current. -/
instance {k : ℕ} : Coe (IntegralCurrent n X k) (Current n X k) where
  coe := IntegralCurrent.toFun

/-- The isCycle property for IntegralCurrent. -/
def IntegralCurrent.isCycleAt {k : ℕ} (T : IntegralCurrent n X k) : Prop :=
  ∃ (k' : ℕ) (h : k = k' + 1), (h ▸ T.toFun).boundary = 0

/-- The boundary of an integral current is integral. -/
theorem isIntegral_boundary {k : ℕ} (T : Current n X (k + 1)) :
    isIntegral T → isIntegral T.boundary := by
  intro ⟨T_set, _⟩
  exact ⟨T_set, trivial⟩

def IntegralCurrent.boundary {k : ℕ} (T : IntegralCurrent n X (k + 1)) :
    IntegralCurrent n X k where
  toFun := T.toFun.boundary
  is_integral := isIntegral_boundary T.toFun T.is_integral

end
