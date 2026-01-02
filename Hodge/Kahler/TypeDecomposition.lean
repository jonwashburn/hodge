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

    This predicate `isPQForm n X p q h ω` asserts that the form ω is of type (p,q).

    Key properties:
    - `zero_is_pq`: the zero form is of type (p,q) for all p,q
    - `isPQForm_wedge`: wedge product of (p,q) and (r,s) forms is of type (p+r, q+s)
    - `omega_is_1_1`: the Kähler form is of type (1,1)
    - `omega_pow_is_p_p`: ω^p is of type (p,p)

    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry",
    Wiley, 1978, Chapter 0, Section 5].
    Reference: [C. Voisin, "Hodge Theory and Complex Algebraic Geometry",
    Vol. I, Cambridge University Press, 2002, Chapter 6]. -/
opaque isPQForm (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (p q : ℕ) {k : ℕ} (h : p + q = k) (ω : SmoothForm n X k) : Prop

/-- A (p,p)-form is a form of type (p,p). (Type decomposition version) -/
def isPPFormTD (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (p : ℕ) (ω : SmoothForm n X (2 * p)) : Prop :=
  isPQForm n X p p (by rw [Nat.two_mul]) ω

/-- **Zero Form Type Stability** (Standard fact). -/
axiom zero_is_pq (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (p q : ℕ) {k : ℕ} (h : p + q = k) : isPQForm n X p q h (0 : SmoothForm n X k)

/-- **Wedge Product Type Stability** (Standard fact). -/
axiom isPQForm_wedge {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {p q r s : ℕ} {k l : ℕ} (hpq : p + q = k) (hrs : r + s = l)
    (ω : SmoothForm n X k) (η : SmoothForm n X l) :
    isPQForm n X p q hpq ω → isPQForm n X r s hrs η →
    isPQForm n X (p + r) (q + s) (by omega) (smoothWedge ω η)

/-! ## Kähler Form Properties -/

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- The Kähler form ω is a (1,1)-form. -/
axiom omega_is_1_1_axiom :
    isPPFormTD n X 1 (K.omega_form)

/-- The Kähler form ω is a (1,1)-form. -/
theorem omega_is_1_1 :
    isPPFormTD n X 1 (K.omega_form) :=
  omega_is_1_1_axiom

/-! ## Kähler Power -/

/-- Helper lemma: 2 + 2*p = 2*(p+1) -/
private theorem two_add_two_mul (p : ℕ) : 2 + 2 * p = 2 * (p + 1) := by ring

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
axiom unitForm_is_0_0 :
    isPQForm n X 0 0 (by rfl) (unitForm (n := n) (X := X))

/-- The p-th power of the Kähler form ω^p is a (p,p)-form. -/
axiom omega_pow_is_p_p_axiom (p : ℕ) : isPPFormTD n X p (kahlerPow (n := n) (X := X) p)

/-- The p-th power of the Kähler form ω^p is a (p,p)-form. -/
theorem omega_pow_is_p_p (p : ℕ) : isPPFormTD n X p (kahlerPow (n := n) (X := X) p) :=
  omega_pow_is_p_p_axiom p

/-! ## Rationality of Kähler Power -/

/-- Helper: type cast preserves closedness.
    If h : k = k' and ω is closed, then h ▸ ω is also closed. -/
private theorem isFormClosed_cast {k k' : ℕ} (h : k = k')
    (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    IsFormClosed (h ▸ ω : SmoothForm n X k') := by
  subst h
  exact hω

/-- **Kähler Power is Closed** (Proved by Induction).

    The exterior derivative of ω^p is zero: d(ω^p) = 0.

    **Proof**: The Kähler form ω is closed (dω = 0) by definition of a Kähler manifold.
    By induction on p:
    - Base case (p = 0): ω^0 = unitForm, which is closed by `unitForm_isClosed`.
    - Inductive step: ω^{p+1} = ω ∧ ω^p. By `isFormClosed_wedge`, the wedge product
      of closed forms is closed. Since ω is closed (`omega_isClosed`) and ω^p is
      closed by the induction hypothesis, ω^{p+1} is closed.

    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry",
    Wiley, 1978, Chapter 0, Section 7]. -/
theorem omega_pow_IsFormClosed (p : ℕ) : IsFormClosed (kahlerPow (n := n) (X := X) p) := by
  induction p with
  | zero =>
    -- ω^0 = unitForm
    simp only [kahlerPow]
    exact unitForm_isClosed
  | succ p ih =>
    -- ω^{p+1} = ω ∧ ω^p (with type cast)
    simp only [kahlerPow]
    -- The cast ▸ preserves closedness
    apply isFormClosed_cast
    -- ω ∧ ω^p is closed because both ω and ω^p are closed
    exact isFormClosed_wedge K.omega_form (kahlerPow p) omega_isClosed ih

/-- **Kähler Power is Rational** (Classical Pillar).

    The cohomology class [ω^p] lies in the rational cohomology H^{2p}(X, ℚ).

    **Mathematical Justification**: For a smooth projective variety X ⊂ ℙ^N,
    the Kähler form ω is the restriction of the Fubini-Study form on ℙ^N.
    The class [ω] is the hyperplane class, which is integral (lies in H²(X, ℤ)).
    Therefore [ω^p] = [ω]^p ∈ H^{2p}(X, ℤ) ⊂ H^{2p}(X, ℚ).

    **Why This is an Axiom**: This is a classical pillar from algebraic geometry
    that requires:
    1. The embedding X ↪ ℙ^N and the Fubini-Study form
    2. The comparison isomorphism between de Rham and singular cohomology
    3. Integrality of the hyperplane class

    These deep results are beyond the current formalization scope.

    Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry",
    Wiley, 1978, Chapter 1, Section 2].
    Reference: [C. Voisin, "Hodge Theory and Complex Algebraic Geometry",
    Vol. I, Cambridge University Press, 2002, Chapter 11]. -/
axiom omega_pow_is_rational (p : ℕ) : isRationalClass ⟦kahlerPow (n := n) (X := X) p, omega_pow_IsFormClosed p⟧

/-- **Theorem: scaled Kähler power is closed.**
    This is the standard fact that \(d(\omega^p)=0\) and hence also
    \(d(\omega^p/p!)=0\). -/
theorem IsFormClosed_omegaPow_scaled (p : ℕ) :
    IsFormClosed ((1 / (p.factorial : ℂ)) • kahlerPow (n := n) (X := X) p) :=
  isFormClosed_smul (omega_pow_IsFormClosed p)

end
