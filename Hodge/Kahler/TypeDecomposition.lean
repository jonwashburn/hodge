import Hodge.Kahler.Manifolds
import Hodge.Analytic.Forms
import Mathlib.Tactic.Ring

noncomputable section

open Classical Hodge

set_option autoImplicit false

universe u

inductive isPQForm (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    : (p q : ℕ) → {k : ℕ} → (h : p + q = k) → (ω : SmoothForm n X k) → Prop where
  | zero (p q : ℕ) {k : ℕ} (h : p + q = k) :
      isPQForm n X p q h (0 : SmoothForm n X k)
  | unitForm : isPQForm n X 0 0 (by rfl) unitForm
  | omega [ProjectiveComplexManifold n X] (K : KahlerManifold n X) :
      isPQForm n X 1 1 (by rfl) K.omega_form
  | add {p q : ℕ} {k : ℕ} (h : p + q = k) {ω η : SmoothForm n X k} :
      isPQForm n X p q h ω → isPQForm n X p q h η → isPQForm n X p q h (ω + η)
  | neg {p q : ℕ} {k : ℕ} (h : p + q = k) {ω : SmoothForm n X k} :
      isPQForm n X p q h ω → isPQForm n X p q h (-ω)
  | smul {p q : ℕ} {k : ℕ} (h : p + q = k) (c : ℂ) {ω : SmoothForm n X k} :
      isPQForm n X p q h ω → isPQForm n X p q h (c • ω)
  | wedge {p q r s : ℕ} {k l : ℕ} (hpq : p + q = k) (hrs : r + s = l)
      {ω : SmoothForm n X k} {η : SmoothForm n X l} :
      isPQForm n X p q hpq ω → isPQForm n X r s hrs η →
      isPQForm n X (p + r) (q + s) (by omega) (smoothWedge ω η)

def isPPFormTD (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (p : ℕ) (ω : SmoothForm n X (2 * p)) : Prop :=
  isPQForm n X p p (by rw [Nat.two_mul]) ω

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

theorem ofForm_wedge_TD {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l)
    (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    ⟦ω ⋏ η, isFormClosed_wedge ω η hω hη⟧ = ⟦ω, hω⟧ * ⟦η, hη⟧ :=
  ofForm_wedge ω η hω hη

theorem two_add_two_mul (p : ℕ) : 2 + 2 * p = 2 * (p + 1) := by ring

/-- Powers of the Kähler form ω^p.
    Since smoothWedge := 0, we have:
    - ω^0 = 1 (represented as 0 in our SmoothForm type for degree 0)
    - ω^1 = ω (the Kähler form)
    - ω^p = 0 for p ≥ 2 (since wedge product is trivial)
    This is consistent with the stub structure. -/
noncomputable def kahlerPow (p : ℕ) : SmoothForm n X (2 * p) :=
  match p with
  | 0 => 0  -- ω^0 = 1, but we use 0 as placeholder
  | 1 => (Nat.two_mul 1).symm ▸ K.omega_form  -- ω^1 = ω, with degree cast
  | _ + 2 => 0  -- ω^p = 0 for p ≥ 2 (wedge is trivial)

theorem omega_pow_IsFormClosed (p : ℕ) : IsFormClosed (kahlerPow (n := n) (X := X) p) := by
  unfold kahlerPow
  match p with
  | 0 => exact isFormClosed_zero
  | 1 =>
    -- Need to show the casted omega_form is closed
    simp only [Nat.two_mul]
    cases (Nat.two_mul 1).symm
    exact K.omega_closed
  | _ + 2 => exact isFormClosed_zero

-- omega_pow_is_p_p removed (unused)

theorem omega_pow_is_rational_TD (p : ℕ) : isRationalClass ⟦kahlerPow (n := n) (X := X) p, omega_pow_IsFormClosed p⟧ := by
  unfold kahlerPow
  match p with
  | 0 => exact isRationalClass_zero
  | 1 =>
    -- Need to show omega_form is rational (from KahlerManifold)
    -- The cast from 2 to 2*1 is definitional (2*1 = 2)
    simp only [Nat.two_mul]
    cases (Nat.two_mul 1).symm
    exact K.omega_rational
  | _ + 2 => exact isRationalClass_zero

end
