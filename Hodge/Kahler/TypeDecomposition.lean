import Hodge.Kahler.Manifolds
import Hodge.Analytic.Forms

/-!
# Track C.2: Type Decomposition
-/

noncomputable section

open Classical

/-! ## (p,q)-Forms -/

/-- A smooth differential form is of type (p,q). -/
axiom isPQForm (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (p q : ℕ) {k : ℕ} (h : p + q = k) (ω : SmoothForm n X k) : Prop

/-- A (p,p)-form is a form of type (p,p). -/
def isPPForm' (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (p : ℕ) (ω : SmoothForm n X (2 * p)) : Prop :=
  isPQForm n X p p (by rw [Nat.two_mul]) ω

/-! ## Kähler Form Properties -/

/-- The Kähler form ω is a (1,1)-form. -/
theorem omega_is_1_1 (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X] :
    isPPForm' n X 1 (K.omega_form) := sorry

/-! ## Kähler Power -/

/-- The p-th power of the Kähler form ω^p. -/
def omegaPow (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p : ℕ) : SmoothForm n X (2 * p) := sorry

/-- The p-th power of the Kähler form ω^p is a (p,p)-form. -/
theorem omega_pow_is_p_p (n : ℕ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p : ℕ) : isPPForm' n X p (omegaPow n X p) := sorry

end
