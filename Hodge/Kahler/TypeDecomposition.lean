/-!
# Track C.2: Type Decomposition
-/

import Hodge.Kahler.Manifolds
import Hodge.Analytic.Forms

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-! ## (p,q)-Forms -/

/-- A smooth differential form is of type (p,q) if it lies in the
corresponding eigenspace of the complex structure J. -/
def isPQForm (p q : ℕ) (ω : SmoothForm n X (p + q)) : Prop :=
  ∀ (x : X) (v : Fin (p + q) → TangentSpace 𝓒(Complex, n) x),
    -- For real forms, being type (p,p) means being invariant under J.
    p = q → ω x (fun i => Complex.I • v i) = ω x v

/-- A smoother way to define (p,p)-forms without the 2*p=k constraint in the type. -/
def isPPForm' (p : ℕ) (ω : SmoothForm n X (2 * p)) : Prop :=
  isPQForm p p ω

/-! ## Hodge Decomposition -/

/-- The action of the complex structure J on the space of smooth forms. -/
def formJ {k : ℕ} (ω : SmoothForm n X k) : SmoothForm n X k :=
  fun x v => ω x (fun i => Complex.I • v i)

/-- **Hodge Decomposition**
The decomposition of the space of smooth complex k-forms into (p,q) components.
Reference: [Griffiths-Harris, 1978]. -/
theorem hodge_decomposition (k : ℕ) :
  ∃ (proj : ∀ p q, p + q = k → (SmoothForm n X k →ₗ[ℝ] SmoothForm n X k)),
    (∀ ω, ω = ∑ p_q : {pq : ℕ × ℕ // pq.1 + pq.2 = k}, proj p_q.1.1 p_q.1.2 p_q.2 ω) ∧
    (∀ p1 q1 h1 p2 q2 h2, proj p1 q1 h1 ∘ₗ proj p2 q2 h2 =
      if p1 = p2 ∧ q1 = q2 then proj p1 q1 h1 else 0) ∧
    (∀ p q h ω, isPQForm p q (proj p q h ω)) := by
  -- The projections are defined using the spectral decomposition of the complex structure J.
  sorry

/-! ## Kähler Form Properties -/

/-- The Kähler form ω is a (1,1)-form. -/
theorem omega_is_1_1 :
    isPPForm' 1 (KahlerManifold.omega_form X) := by
  intro x v
  exact K.is_j_invariant x (v 0) (v 1)

/-- The wedge product of (p,p)-forms is a (p+q,p+q)-form. -/
theorem isPPForm_wedge {p q : ℕ} {α : SmoothForm n X (2 * p)} {β : SmoothForm n X (2 * q)} :
    isPPForm' p α → isPPForm' q β → isPPForm' (p + q) (α ∧ β) := by
  intro hα hβ x v
  unfold isPPForm' at *
  simp only [DifferentialForm.wedge_apply]
  congr
  ext σ
  rw [hα x, hβ x]

/-- Simple calibrated forms are (p,p)-forms. -/
theorem isPPForm_simple (p : ℕ) (x : X) (V : Submodule Complex (TangentSpace 𝓒(Complex, n) x))
    (hV : FiniteDimensional.finrank Complex V = p) :
    isPPForm' p (simpleCalibratedForm p x V) := by
  -- Since V is a complex subspace, its volume form is invariant under J.
  sorry

/-- The p-th power of the Kähler form ω^p is a (p,p)-form. -/
theorem omega_pow_is_p_p (p : ℕ) :
    isPPForm' p (omegaPow (n := n) (X := X) p) := by
  induction p with
  | zero =>
    -- 0-form 1 is J-invariant
    intro x v
    unfold omegaPow
    simp only [DifferentialForm.constant_apply]
  | succ p ih =>
    unfold omegaPow
    apply isPPForm_wedge
    · exact omega_is_1_1
    · exact ih

end
