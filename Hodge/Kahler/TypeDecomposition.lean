import Hodge.Kahler.Manifolds
import Hodge.Analytic.Forms

/-!
# Track C.2: Type Decomposition
-/

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-! ## (p,q)-Forms -/

/-- A smooth differential form is of type (p,q) if p+q=k and it lies in the
corresponding eigenspace of the complex structure J.

Mathematically, ω is of type (p,q) if under the J-action on the cotangent bundle,
ω transforms with eigenvalue i^p · (-i)^q = i^{p-q}.

Reference: [Griffiths-Harris, 1978, p. 116]. -/
axiom isPQForm (p q : ℕ) {k : ℕ} (h : p + q = k) (ω : SmoothForm n X k) : Prop

/-- Axiom: Linearity of the (p,q) property. -/
axiom isPQForm_add {p q : ℕ} {k : ℕ} (h : p + q = k) {α β : SmoothForm n X k} :
    isPQForm p q h α → isPQForm p q h β → isPQForm p q h (α + β)

/-- Axiom: Scalar multiplication preserves (p,q) type. -/
axiom isPQForm_smul {p q : ℕ} {k : ℕ} (h : p + q = k) {α : SmoothForm n X k} (c : ℂ) :
    isPQForm p q h α → isPQForm p q h (c • α)

/-- Axiom: Zero form is of any type (p,q). -/
axiom isPQForm_zero {p q : ℕ} {k : ℕ} (h : p + q = k) :
    isPQForm p q h 0

/-- Axiom: Wedge product of (p,q) forms. -/
axiom isPQForm_wedge_raw {p q r s : ℕ} {k l : ℕ} (hpq : p + q = k) (hrs : r + s = l)
    {α : SmoothForm n X k} {β : SmoothForm n X l} :
    isPQForm p q hpq α → isPQForm r s hrs β →
    isPQForm (p + r) (q + s) (by rw [← hpq, ← hrs, add_add_add_comm]) (wedge α β)

/-- A (p,p)-form is a form of type (p,p). -/
def isPPForm' (p : ℕ) (ω : SmoothForm n X (2 * p)) : Prop :=
  isPQForm p p (by rw [Nat.two_mul]) ω

/-! ## Hodge Decomposition -/

/-- **Hodge Decomposition**
The decomposition of the space of smooth k-forms into (p,q) components.
Reference: [Griffiths-Harris, 1978, p. 116]. -/
axiom hodge_decomposition (k : ℕ) :
  ∃ (proj : ∀ p q, p + q = k → (SmoothForm n X k →ₗ[ℝ] SmoothForm n X k)),
    (∀ p q h ω, isPQForm p q h (proj p q h ω)) ∧
    (∀ ω, (∑ pq in (Finset.natAntidiagonal k), proj pq.1 pq.2 pq.2.2 ω) = ω)

/-! ## Kähler Form Properties -/

/-- Axiom: The Kähler form ω is a (1,1)-form. -/
axiom omega_is_1_1 :
    isPPForm' 1 (K.omega_form)

/-- The wedge product of (p,p)-forms is a (p+q,p+q)-form. -/
theorem isPPForm_wedge {p q : ℕ} {α : SmoothForm n X (2 * p)} {β : SmoothForm n X (2 * q)} :
    isPPForm' p α → isPPForm' q β → isPPForm' (p + q) (cast (by rw [Nat.mul_add]) (wedge α β)) := by
  intro hα hβ
  let h_wedge := isPQForm_wedge_raw (Nat.two_mul p) (Nat.two_mul q) hα hβ
  rw [← Nat.left_distrib] at h_wedge
  exact h_wedge

/-! ## Kähler Power -/

/-- The p-th power of the Kähler form ω^p.
    ω^0 is the identity (axiomatized), ω^{p+1} = ω ∧ ω^p. -/
def omegaPow : (p : ℕ) → SmoothForm n X (2 * p)
  | 0 => ⟨fun _ => AlternatingMap.constOfIsEmpty ℂ _ 1⟩
  | p + 1 => cast (by rw [Nat.mul_succ, Nat.add_comm]) (wedge K.omega_form (omegaPow p))

/-- Axiom: The constant 1-form is of type (0,0). -/
axiom isPQForm_one :
    isPQForm 0 0 (by rw [Nat.add_zero]) ⟨fun _ => AlternatingMap.constOfIsEmpty ℂ _ 1⟩

/-- The p-th power of the Kähler form ω^p is a (p,p)-form. -/
theorem omega_pow_is_p_p (p : ℕ) :
    isPPForm' p (omegaPow (n := n) (X := X) p) := by
  induction p with
  | zero =>
      unfold omegaPow
      exact isPQForm_one
  | succ p ih =>
      unfold omegaPow
      -- Use isPPForm_wedge
      have h := isPPForm_wedge (p := 1) (q := p) omega_is_1_1 ih
      exact h

/-- Simple calibrated forms are (p,p)-forms.

Mathematically, given a complex p-dimensional subspace V of T_x X,
the simple calibrated form is the volume form of V extended to a global form.

Reference: [Harvey-Lawson, 1982, p. 17]. -/
axiom simpleCalibratedFormLocal (p : ℕ) (x : X) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x)) :
    SmoothForm n X (2 * p)

/-- Simple calibrated forms are (p,p)-forms. -/
axiom isPPForm_simple (p : ℕ) (x : X) (V : Submodule ℂ (TangentSpace (𝓒_complex n) x))
    (hV : Module.finrank ℂ V = p) :
    isPPForm' p (simpleCalibratedFormLocal p x V)

end
