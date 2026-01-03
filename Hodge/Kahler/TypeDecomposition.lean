import Hodge.Kahler.Manifolds
import Hodge.Analytic.Forms
import Mathlib.Tactic.Ring

/-!

This file defines the type decomposition of differential forms on complex manifolds.


- `isPQForm`: Predicate for a form being of type (p,q)
- `isPPFormTD`: Predicate for a form being of type (p,p), specific to this file
- `kahlerPow`: The p-th power of the Kähler form ω^p


On a complex manifold of dimension n, differential k-forms decompose as:
  Ω^k = ⊕_{p+q=k} Ω^{p,q}

where Ω^{p,q} consists of forms locally expressible as:
  ∑ f_{I,J} dz^{i₁} ∧ ... ∧ dz^{i_p} ∧ dz̄^{j₁} ∧ ... ∧ dz̄^{j_q}

The Kähler form ω is the canonical (1,1)-form on a Kähler manifold.
-/

noncomputable section

open Classical

set_option autoImplicit false

universe u

/-! ## (p,q)-Forms -/

/-- **(p,q)-Type Decomposition** (Hodge Decomposition).

    On a complex manifold X, the space of smooth k-forms decomposes as:

    A^k(X) = ⊕_{p+q=k} A^{p,q}(X)

    where A^{p,q}(X) consists of forms of type (p,q), meaning forms that are
    locally expressible as sums of terms involving p holomorphic differentials
    dz_i and q anti-holomorphic differentials dz̄_j.

    This inductive predicate `isPQForm n X p q h ω` asserts that the form ω is of type (p,q).
    A form is of type (p,q) if it can be constructed from:
    - The zero form (of any type)
    - Sums of (p,q)-forms
    - Scalar multiples of (p,q)-forms
    - Wedge products of (p₁,q₁) and (p₂,q₂) forms giving (p₁+p₂, q₁+q₂)
    - The Kähler form ω (which is (1,1)) - added via omega_is_1_1_axiom
    - The unit form (which is (0,0)) - added via unitForm_is_0_0 -/
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

/-- A (p,p)-form is a form of type (p,p). (Type decomposition version) -/
def isPPFormTD (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (p : ℕ) (ω : SmoothForm n X (2 * p)) : Prop :=
  isPQForm n X p p (by rw [Nat.two_mul]) ω

/-- **Zero Form Type Stability** (Theorem from inductive definition). -/
theorem zero_is_pq (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (p q : ℕ) {k : ℕ} (h : p + q = k) : isPQForm n X p q h (0 : SmoothForm n X k) :=
  isPQForm.zero p q h

/-- **Wedge Product Type Stability** (Theorem from inductive definition). -/
theorem isPQForm_wedge {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {p q r s : ℕ} {k l : ℕ} (hpq : p + q = k) (hrs : r + s = l)
    (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    isPQForm n X p q hpq ω → isPQForm n X r s hrs η →
    isPQForm n X (p + r) (q + s) (by omega) (smoothWedge ω η) :=
  isPQForm.wedge hpq hrs

/-! ## Kähler Form Properties -/

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- The Kähler form ω is a (1,1)-form. -/
theorem omega_is_1_1 :
    isPPFormTD n X 1 (K.omega_form) :=
  isPQForm.omega K

/-! ## Kähler Power -/

/-- Helper lemma: 2 + 2 * p = 2 * (p + 1) -/
theorem two_add_two_mul (p : ℕ) : 2 + 2 * p = 2 * (p + 1) := by ring

/-- Cast a form from degree k to degree l when k = l. -/
def SmoothForm.cast {k l : ℕ} (h : k = l) (ω : SmoothForm n X k) : SmoothForm n X l :=
  h ▸ ω

/-- Casting preserves closedness. -/
theorem isFormClosed_cast {k l : ℕ} (h : k = l) (ω : SmoothForm n X k) :
    IsFormClosed ω → IsFormClosed (SmoothForm.cast h ω) := by
  intro hω
  subst h
  exact hω

/-- The p-th power of the Kähler form ω^p.

This is defined recursively:
- ω^0 = 1 (the unit form)
- ω^{p+1} = ω ⋀ ω^p

The form ω^p is a (p,p)-form of degree 2p. -/
def kahlerPow (p : ℕ) : SmoothForm n X (2 * p) :=
  match p with
  | 0 => unitForm
  | p + 1 => (two_add_two_mul p) ▸ (K.omega_form ⋏ kahlerPow p)

/-- The unit form is of type (0,0). -/
theorem unitForm_is_0_0 :
    isPQForm n X 0 0 (by rfl) (unitForm (n := n) (X := X)) :=
  isPQForm.unitForm

/-- Casting preserves isPQForm type. -/
theorem isPQForm_cast {k l : ℕ} (h : k = l) (ω : SmoothForm n X k) (p q : ℕ)
    (hpq : p + q = k) (hpq' : p + q = l) :
    isPQForm n X p q hpq ω → isPQForm n X p q hpq' (SmoothForm.cast h ω) := by
  subst h
  simp only [SmoothForm.cast]
  exact id

/-- isPQForm is stable under proof-irrelevant changes to type indices.
    If (p,q) = (p',q') and the degree proofs are compatible, the property transfers. -/
theorem isPQForm_eq {p q p' q' : ℕ} {k : ℕ} (hp : p = p') (hq : q = q')
    (hpq : p + q = k) (hpq' : p' + q' = k) (ω : SmoothForm n X k) :
    isPQForm n X p q hpq ω → isPQForm n X p' q' hpq' ω := by
  subst hp hq
  exact id

/-- The p-th power of the Kähler form ω^p is a (p,p)-form.

**Proof**: By induction on p:
- Base case (p=0): ω^0 = unitForm, which is (0,0) by `unitForm_is_0_0`.
- Inductive step: ω^{p+1} = ω ∧ ω^p. By `isPQForm_wedge`, since ω is (1,1)
  (by `omega_is_1_1`) and ω^p is (p,p) (by IH), ω ∧ ω^p is (1+p, 1+p) = (p+1, p+1). -/
theorem omega_pow_is_p_p (p : ℕ) : isPPFormTD n X p (kahlerPow (n := n) (X := X) p) := by
  induction p with
  | zero =>
    -- Base case: kahlerPow 0 = unitForm, which is (0,0)
    unfold isPPFormTD kahlerPow
    exact unitForm_is_0_0
  | succ p ih =>
    -- Inductive step: kahlerPow (p+1) = (two_add_two_mul p) ▸ (ω ⋏ kahlerPow p)
    unfold isPPFormTD kahlerPow
    -- ω is (1,1) and kahlerPow p is (p,p), so wedge is (1+p, 1+p)
    have h_omega : isPQForm n X 1 1 (by rfl) K.omega_form := omega_is_1_1
    have h_pow : isPQForm n X p p (by omega) (kahlerPow p) := ih
    -- By isPQForm_wedge, wedge product preserves types
    -- We get (1+p, 1+p) which equals (p+1, p+1)
    have h_wedge : isPQForm n X (1 + p) (1 + p) (by omega) (K.omega_form ⋏ kahlerPow p) :=
      isPQForm_wedge (by rfl) (by omega) K.omega_form (kahlerPow p) h_omega h_pow
    -- Cast the form to the right degree
    have h_cast : isPQForm n X (1 + p) (1 + p) (by omega)
        ((two_add_two_mul p) ▸ (K.omega_form ⋏ kahlerPow p)) :=
      isPQForm_cast (two_add_two_mul p) _ (1 + p) (1 + p) (by omega) (by omega) h_wedge
    -- Now use isPQForm_eq to convert (1+p, 1+p) to (p+1, p+1)
    exact isPQForm_eq (Nat.add_comm 1 p) (Nat.add_comm 1 p) (by omega) (by omega) _ h_cast

/-! ## Rationality of Kähler Power -/

/-- **Kähler Power is Closed** (Proved by Induction).

    The exterior derivative of ω^p is zero: d(ω^p) = 0.

    **Proof**: By induction on p:
    - Base case (p=0): ω^0 = unitForm (the constant 1-form), which is closed
      by `unitForm_isClosed`.
    - Inductive step: ω^{p+1} = ω ∧ ω^p. By `isFormClosed_wedge`, since dω = 0
      (by `omega_isClosed`) and d(ω^p) = 0 (by induction hypothesis), we have
      d(ω ∧ ω^p) = 0.

    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry",
    Wiley, 1978, Chapter 0, Section 7]. -/
theorem omega_pow_IsFormClosed (p : ℕ) : IsFormClosed (kahlerPow (n := n) (X := X) p) := by
  induction p with
  | zero => exact unitForm_isClosed
  | succ p ih =>
    unfold kahlerPow
    apply isFormClosed_cast
    exact isFormClosed_wedge K.omega_form (kahlerPow p) omega_isClosed ih

/-- **Wedge Product Induces Cup Product on Cohomology** (de Rham Theorem).

    The wedge product of closed forms represents the cup product of their
    cohomology classes. This is the fundamental compatibility between the
    wedge product on differential forms and the cup product on cohomology.

    [ω ∧ η] = [ω] ∪ [η]

    **Proof**: Follows by definition of the cup product on cohomology classes.

    Reference: [Bott-Tu, "Differential Forms in Algebraic Topology", 1982, §5]. -/
theorem ofForm_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l)
    (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    ⟦ω ⋏ η, isFormClosed_wedge ω η hω hη⟧ = ⟦ω, hω⟧ * ⟦η, hη⟧ :=
  rfl

/-- Cohomology class of cast form equals cohomology class of original (by proof irrelevance). -/
theorem ofForm_cast {k l : ℕ} (h : k = l) (ω : SmoothForm n X k) (hω : IsFormClosed ω)
    (hcast : IsFormClosed (SmoothForm.cast h ω)) :
    ⟦SmoothForm.cast h ω, hcast⟧ = h ▸ ⟦ω, hω⟧ := by
  subst h
  apply ofForm_proof_irrel

/-- Rationality is preserved under transport along degree equality. -/
theorem isRationalClass_cast {k l : ℕ} (h : k = l)
    (c : DeRhamCohomologyClass n X k) :
    isRationalClass c → isRationalClass (h ▸ c) := by
  intro hc
  subst h
  exact hc

/-- Helper: cohomology class of degree-cast form equals cast of cohomology class.
    This uses the fact that ▸ on a quotient lifts through the quotient. -/
theorem ofForm_transport {k l : ℕ} (h : k = l) (ω : SmoothForm n X k) (hω : IsFormClosed ω)
    (hcast : IsFormClosed (h ▸ ω)) :
    ⟦h ▸ ω, hcast⟧ = h ▸ ⟦ω, hω⟧ := by
  subst h
  rfl

/-- **Kähler Power is Rational** (Theorem via Induction).

    The cohomology class [ω^p] lies in the rational cohomology H^{2p}(X, ℚ).

    **Proof**: By induction on p:
    - Base case (p=0): [ω^0] = [1] is rational by `unitForm_is_rational`.
    - Inductive step: [ω^{p+1}] = [ω ∧ ω^p] = [ω] · [ω^p] by `ofForm_wedge`.
      By `isRationalClass_mul`, since [ω] is rational (by `omega_is_rational`)
      and [ω^p] is rational (by IH), the product [ω^{p+1}] is rational.

    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry",
    Wiley, 1978, Chapter 1, Section 2].
    Reference: [C. Voisin, "Hodge Theory and Complex Algebraic Geometry",
    Vol. I, Cambridge University Press, 2002, Chapter 11]. -/
theorem omega_pow_is_rational (p : ℕ) : isRationalClass ⟦kahlerPow (n := n) (X := X) p, omega_pow_IsFormClosed p⟧ := by
  induction p with
  | zero =>
    -- Base case: kahlerPow 0 = unitForm
    unfold kahlerPow
    exact unitForm_is_rational
  | succ p ih =>
    -- Inductive step: kahlerPow (p+1) = (two_add_two_mul p) ▸ (ω ⋏ kahlerPow p)
    have h_wedge_closed : IsFormClosed (K.omega_form ⋏ kahlerPow p) :=
      isFormClosed_wedge K.omega_form (kahlerPow p) omega_isClosed (omega_pow_IsFormClosed p)
    have h_wedge_eq : ⟦K.omega_form ⋏ kahlerPow p, h_wedge_closed⟧ =
                      ⟦K.omega_form, omega_isClosed⟧ * ⟦kahlerPow p, omega_pow_IsFormClosed p⟧ :=
      ofForm_wedge K.omega_form (kahlerPow p) omega_isClosed (omega_pow_IsFormClosed p)
    have h_omega_rat : isRationalClass ⟦K.omega_form, omega_isClosed⟧ := omega_is_rational
    have h_mul_rat := isRationalClass_mul ⟦K.omega_form, omega_isClosed⟧
                      ⟦kahlerPow p, omega_pow_IsFormClosed p⟧ h_omega_rat ih
    have h_wedge_rat : isRationalClass ⟦K.omega_form ⋏ kahlerPow p, h_wedge_closed⟧ := by
      rw [h_wedge_eq]; exact h_mul_rat
    unfold kahlerPow
    -- Goal: isRationalClass ⟦(two_add_two_mul p) ▸ (ω ⋏ kahlerPow p), omega_pow_IsFormClosed (p + 1)⟧
    rw [ofForm_transport (two_add_two_mul p) (K.omega_form ⋏ kahlerPow p) h_wedge_closed
        (omega_pow_IsFormClosed (p + 1))]
    exact isRationalClass_cast (two_add_two_mul p) _ h_wedge_rat

/-- **Theorem: scaled Kähler power is closed.**
    This is the standard fact that \(d(\omega^p)=0\) and hence also
    \(d(\omega^p/p!)=0\). -/
theorem IsFormClosed_omegaPow_scaled (p : ℕ) :
    IsFormClosed ((1 / (p.factorial : ℂ)) • kahlerPow (n := n) (X := X) p) :=
  isFormClosed_smul (omega_pow_IsFormClosed p)

end
