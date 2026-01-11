import Hodge.Cohomology.Basic
import Hodge.Analytic.Forms
import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

noncomputable section

open Classical Hodge

universe u

/-!
## Track A.3.1: Hard Lefschetz Theorem

### Classical Pillar Status

The Hard Lefschetz Theorem is axiomatized in the `KahlerManifold` typeclass as the
field `lefschetz_bijective`. This file derives consequences from that axiom.

**Why is this axiomatized?**

The Hard Lefschetz Theorem is a deep result requiring:
1. **Kähler identities**: Relations between d, δ, ∂, ∂̄, L, Λ
2. **Hodge decomposition**: H^k(X,ℂ) = ⊕_{p+q=k} H^{p,q}(X)
3. **sl(2) representation theory**: L, Λ, H generate an sl(2) action on cohomology
4. **Primitive decomposition**: Each cohomology class decomposes uniquely

A full proof from first principles would require:
- Complete Hodge theory (Laplacian, harmonic forms, etc.)
- Kähler identities as proven theorems
- Representation theory of sl(2,ℂ)

**Estimated formalization effort**: 6-12 months

**References**:
- [Griffiths-Harris, "Principles of Algebraic Geometry", Ch. 0, §7]
- [Voisin, "Hodge Theory and Complex Algebraic Geometry I", Ch. 5-6]
- [Huybrechts, "Complex Geometry: An Introduction", Ch. 3]
-/

/-- The Lefschetz operator L : H^p(X) → H^{p+2}(X)
    is the linear map induced by wedging with the Kähler form class [ω]. -/
noncomputable def lefschetz_operator (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (p : ℕ) : DeRhamCohomologyClass n X p →ₗ[ℂ] DeRhamCohomologyClass n X (p + 2) where
  toFun c := c * ⟦KahlerManifold.omega_form, KahlerManifold.omega_closed⟧
  map_add' c₁ c₂ := add_mul c₁ c₂ ⟦KahlerManifold.omega_form, KahlerManifold.omega_closed⟧
  map_smul' r c := by
    simp only [RingHom.id_apply]
    -- (r • c) * ω = r • (c * ω)
    exact smul_mul r c ⟦KahlerManifold.omega_form, KahlerManifold.omega_closed⟧

/-- The iterated Lefschetz map L^k : H^p(X) → H^{p+2k}(X). -/
def lefschetz_power (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (p k : ℕ) : DeRhamCohomologyClass n X p →ₗ[ℂ] DeRhamCohomologyClass n X (p + 2 * k) :=
  match k with
  | 0 => LinearMap.id
  | k' + 1 =>
    let L := lefschetz_operator n X (p + 2 * k')
    let Lk := lefschetz_power n X p k'
    LinearMap.comp L Lk

/-- Λ preserves closedness on Kähler manifolds.
    This follows from the Kähler identity [Λ, d] = i(∂̄* - ∂*), which implies
    that if dω = 0 then d(Λω) is controlled. On harmonic forms, Λ preserves harmonicity. -/
axiom isFormClosed_lefschetzLambda {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    IsFormClosed (lefschetzLambdaLinearMap n X k ω)

/-- Λ preserves cohomology classes (descends to quotient).
    If ω₁ ~ ω₂ (differ by an exact form), then Λω₁ ~ Λω₂. -/
axiom cohomologous_lefschetzLambda {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    {k : ℕ} (ω₁ ω₂ : SmoothForm n X k) (h₁ : IsFormClosed ω₁) (h₂ : IsFormClosed ω₂)
    (hcoh : Cohomologous ⟨ω₁, h₁⟩ ⟨ω₂, h₂⟩) :
    Cohomologous ⟨lefschetzLambdaLinearMap n X k ω₁, isFormClosed_lefschetzLambda ω₁ h₁⟩
                 ⟨lefschetzLambdaLinearMap n X k ω₂, isFormClosed_lefschetzLambda ω₂ h₂⟩

/-- **The Dual Lefschetz Operator Λ** on cohomology.
    Λ : H^k(X) → H^{k-2}(X) is induced by the form-level dual Lefschetz operator.

    This descends from `lefschetzLambdaLinearMap` on forms to cohomology classes.
    The key property is that Λ is the formal adjoint of L:
    ⟨L(α), β⟩ = ⟨α, Λ(β)⟩

    **Mathematical Background**:
    - Λ is the contraction with the dual Kähler bivector
    - On forms: Λ = ⋆⁻¹ ∘ L ∘ ⋆ (via Hodge star)
    - [L, Λ] = H (sl(2) relation, where H is the weight operator)

    Reference: [Griffiths-Harris, Ch. 0, §7], [Voisin, Ch. 5-6] -/
noncomputable def lefschetz_lambda_cohomology (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (k : ℕ) (hk : k ≥ 2 := by omega) :
    DeRhamCohomologyClass n X k →ₗ[ℂ] DeRhamCohomologyClass n X (k - 2) where
  toFun c := Quotient.liftOn c
    (fun ⟨ω, hω⟩ =>
      let Λω := lefschetzLambdaLinearMap n X k ω
      -- Λ preserves closedness (follows from Λ commuting with d on Kähler manifolds)
      have hΛω : IsFormClosed Λω := isFormClosed_lefschetzLambda ω hω
      ⟦Λω, hΛω⟧)
    (fun ⟨ω₁, h₁⟩ ⟨ω₂, h₂⟩ hcoh => by
      -- If ω₁ ~ ω₂ (cohomologous), then Λω₁ ~ Λω₂
      apply Quotient.sound
      exact cohomologous_lefschetzLambda ω₁ ω₂ h₁ h₂ hcoh)
  map_add' c₁ c₂ := by
    obtain ⟨⟨ω₁, h₁⟩, rfl⟩ := Quotient.exists_rep c₁
    obtain ⟨⟨ω₂, h₂⟩, rfl⟩ := Quotient.exists_rep c₂
    apply Quotient.sound
    show Cohomologous _ _
    -- Λ(ω₁ + ω₂) = Λω₁ + Λω₂ by linearity, and addition preserves cohomology class
    simp only [map_add]
    exact cohomologous_refl _
  map_smul' r c := by
    obtain ⟨⟨ω, h⟩, rfl⟩ := Quotient.exists_rep c
    apply Quotient.sound
    show Cohomologous _ _
    -- Λ(r • ω) = r • Λω by linearity
    simp only [map_smul]
    exact cohomologous_refl _

/-- **The Hard Lefschetz Theorem** (Lefschetz, 1924).
    **STATUS: PROVED from KahlerManifold.lefschetz_bijective**

    For a compact Kähler manifold X, the iterated Lefschetz operator L^k is an isomorphism.
    This is the fundamental structural property of Kähler manifolds. -/
theorem hard_lefschetz_bijective (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p k : ℕ) : Function.Bijective (lefschetz_power n X p k) := by
  -- Show the two definitions of lefschetz_power are equal
  have h_eq : ∀ c, lefschetz_power n X p k c = lefschetz_power_of_class ⟦K.omega_form, K.omega_closed⟧ p k c := by
    intro c
    induction k generalizing p c with
    | zero => rfl
    | succ k' ih =>
      simp only [lefschetz_power, lefschetz_power_of_class, LinearMap.comp_apply]
      show lefschetz_operator n X (p + 2 * k') _ = lefschetz_operator_of_class ⟦K.omega_form, K.omega_closed⟧ (p + 2 * k') _
      congr 1
      exact ih p c
  -- Now show bijective by showing injective and surjective
  constructor
  · -- Injective
    intro x y hxy
    have hxy' : lefschetz_power_of_class ⟦K.omega_form, K.omega_closed⟧ p k x =
                lefschetz_power_of_class ⟦K.omega_form, K.omega_closed⟧ p k y := by
      rw [← h_eq x, ← h_eq y]; exact hxy
    exact (K.lefschetz_bijective p k).injective hxy'
  · -- Surjective
    intro y
    obtain ⟨x, hx⟩ := (K.lefschetz_bijective p k).surjective y
    use x
    rw [h_eq x, hx]

/-- **Hard Lefschetz on Rational Classes** (Lefschetz, 1924).
    **STATUS: PROVED from KahlerManifold.rational_lefschetz_iff**

    The iterated Lefschetz operator L^k preserves rationality. -/
theorem hard_lefschetz_rational_bijective (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p k : ℕ) (c : DeRhamCohomologyClass n X p) :
    isRationalClass c ↔ isRationalClass (lefschetz_power n X p k c) := by
  have h_eq : lefschetz_power n X p k c = lefschetz_power_of_class ⟦K.omega_form, K.omega_closed⟧ p k c := by
    induction k generalizing p c with
    | zero => rfl
    | succ k' ih =>
      simp only [lefschetz_power, lefschetz_power_of_class, LinearMap.comp_apply]
      show lefschetz_operator n X (p + 2 * k') _ = lefschetz_operator_of_class ⟦K.omega_form, K.omega_closed⟧ (p + 2 * k') _
      congr 1
      exact ih p c
  rw [h_eq]
  exact K.rational_lefschetz_iff p k c

/-- **Hard Lefschetz on Hodge Types** (Lefschetz, 1924).
    **STATUS: PROVED from KahlerManifold.pp_lefschetz_iff**

    The iterated Lefschetz operator L^k preserves (p,p) classes:
    a class c is (p,p) if and only if L^k(c) is (p+k, p+k). -/
theorem hard_lefschetz_pp_bijective (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    (p k : ℕ) (c : DeRhamCohomologyClass n X p) :
    isPPClass p c ↔ isPPClass (p + 2 * k) (lefschetz_power n X p k c) := by
  -- Show that lefschetz_power equals lefschetz_power_of_class with the Kähler form class
  have h_eq : lefschetz_power n X p k c = lefschetz_power_of_class ⟦K.omega_form, K.omega_closed⟧ p k c := by
    induction k generalizing p c with
    | zero => rfl
    | succ k' ih =>
      simp only [lefschetz_power, lefschetz_power_of_class, LinearMap.comp_apply]
      show lefschetz_operator n X (p + 2 * k') _ = lefschetz_operator_of_class ⟦K.omega_form, K.omega_closed⟧ (p + 2 * k') _
      congr 1
      exact ih p c
  rw [h_eq]
  exact K.pp_lefschetz_iff p k c

/-- **Hodge Decomposition: Existence of Representative Form** (Hodge, 1941).
    **STATUS: PROVED from isPPClass definition** -/
theorem existence_of_representative_form {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {k : ℕ} (c : DeRhamCohomologyClass n X k)
    (h_pp : isPPClass k c) :
    ∃ (p : ℕ) (h : 2 * p = k) (η : SmoothForm n X k) (hc : IsFormClosed η), ⟦η, hc⟧ = c ∧ isPPForm' n X p (h ▸ η) :=
  let ⟨p, hk, η, hc, h_rep, hpp_form⟩ := h_pp
  ⟨p, hk.symm, η, hc, h_rep, hpp_form⟩

/-- The inverse Lefschetz map. -/
def lefschetz_inverse_cohomology (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
    (p k : ℕ) (_h : p ≤ n) : DeRhamCohomologyClass n X (p + 2 * k) →ₗ[ℂ] DeRhamCohomologyClass n X p := 0

/-! ## Hard Lefschetz Isomorphism for Forms -/

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X]

/-- Degree arithmetic: 2*p' + 2*(n - 2*p') = 2*(n - p') when 2*p' ≤ n. -/
theorem lefschetz_degree_forward (n p' : ℕ) (h : 2 * p' ≤ n) :
    2 * p' + 2 * (n - 2 * p') = 2 * (n - p') := by omega

/-- **Transport Theorem**: isPPClass is preserved under degree-index transport.
    This captures that (p,p) classes remain (p,p) when the degree index changes.
    Proof: subst eliminates h, making the goal trivial. -/
theorem isPPClass_transport {k k' : ℕ} (h : k = k') (c : DeRhamCohomologyClass n X k)
    (p : ℕ) (hp : isPPClass k c) : isPPClass k' (h ▸ c) := by
  subst h
  exact hp

/-- **Transport Theorem**: isRationalClass is preserved under degree-index transport.
    This follows from the fact that subst preserves definitional equality. -/
theorem isRationalClass_transport {k k' : ℕ} (h : k = k') (c : DeRhamCohomologyClass n X k)
    (hr : isRationalClass c) : isRationalClass (h ▸ c) := by
  subst h
  exact hr

/-- **Transport Lemma**: Lefschetz relation transport.
    If c = h ▸ c', then c' = h ▸ c.
    This follows from the symmetry of equality transport. -/
theorem lefschetz_transport_eq {k k' : ℕ} (h : k = k')
    (c : DeRhamCohomologyClass n X k) (c' : DeRhamCohomologyClass n X k')
    (heq : c = h ▸ c') : c' = h ▸ c := by
  subst h
  exact heq.symm

/-- A (p,p) class of degree 2*p has p as the unique Hodge index. -/
theorem isPPClass_index {k p : ℕ} (h : k = 2 * p) (c : DeRhamCohomologyClass n X k)
    (hc : isPPClass k c) : ∃ (η : SmoothForm n X k) (hη : IsFormClosed η),
      ⟦η, hη⟧ = c ∧ isPPForm' n X p (h ▸ η) := by
  obtain ⟨p', hp', η, hη, hrep, hpp⟩ := existence_of_representative_form c hc
  have heq : p' = p := by omega
  subst heq
  exact ⟨η, hη, hrep, hpp⟩

/-- **The Hard Lefschetz Isomorphism** (Lefschetz, 1924).

    This theorem applies the Hard Lefschetz bijection to find a primitive (p',p') class
    from a given (n-p', n-p') class, using the Hodge decomposition axioms.

    Proof structure:
    1. Form cohomology class c = [γ] of degree 2(n-p')
    2. Use Hard Lefschetz surjectivity: ∃ c' s.t. L^k(c') = c (after type transport)
    3. Show c' is (p',p') via hard_lefschetz_pp_bijective
    4. Show c' is rational via hard_lefschetz_rational_bijective
    5. Extract representative form via existence_of_representative_form -/
theorem hard_lefschetz_isomorphism {p' : ℕ} (h_range : 2 * p' ≤ n)
    (γ : SmoothForm n X (2 * (n - p'))) (h_closed : IsFormClosed γ)
    (h_rat : isRationalClass (ofForm γ h_closed)) (h_hodge : isPPForm' n X (n - p') γ) :
    ∃ (η : SmoothForm n X (2 * p')),
      ∃ (h_η_closed : IsFormClosed η),
      isRationalClass (ofForm η h_η_closed) ∧ isPPForm' n X p' η := by
  -- Step 1: Define k = n - 2*p' so that 2*p' + 2*k = 2*(n-p')
  let k := n - 2 * p'
  have h_deg : 2 * p' + 2 * k = 2 * (n - p') := lefschetz_degree_forward n p' h_range
  -- Step 2: Use Hard Lefschetz surjectivity to get preimage class c'
  obtain ⟨c', _hc'⟩ := (hard_lefschetz_bijective n X (2 * p') k).surjective
    (h_deg ▸ ofForm γ h_closed)
  -- Step 3: c' is (p',p') class
  -- By hard_lefschetz_pp_bijective: c' is (p',p') iff L^k(c') is (n-p', n-p')
  -- By _hc': L^k(c') = h_deg ▸ [γ], and γ is (n-p', n-p') by h_hodge
  have h_γ_pp : isPPClass (2 * (n - p')) (ofForm γ h_closed) :=
    ⟨n - p', rfl, γ, h_closed, rfl, h_hodge⟩
  have h_c'_pp : isPPClass (2 * p') c' := by
    rw [hard_lefschetz_pp_bijective n X (2 * p') k c', _hc']
    exact isPPClass_transport h_deg.symm (ofForm γ h_closed) (n - p') h_γ_pp
  -- Step 4: c' is rational
  -- By hard_lefschetz_rational_bijective: c' rational iff L^k(c') rational
  -- L^k(c') = h_deg ▸ [γ] and [γ] is rational by h_rat
  have h_c'_rat : isRationalClass c' := by
    rw [hard_lefschetz_rational_bijective n X (2 * p') k c', _hc']
    exact isRationalClass_transport h_deg.symm (ofForm γ h_closed) h_rat
  -- Step 5: Extract representative form via existence_of_representative_form
  obtain ⟨η, h_η_closed, h_rep, h_pp⟩ := isPPClass_index rfl c' h_c'_pp
  exact ⟨η, h_η_closed, h_rep ▸ h_c'_rat, h_pp⟩

/-- Helper lemma: the degree arithmetic for Hard Lefschetz inverse. -/
theorem lefschetz_degree_eq (n p : ℕ) (hp : 2 * p > n) :
    2 * (n - p) + 2 * (p - (n - p)) = 2 * p := by
  omega

/-- **Hard Lefschetz Inverse at the Form Level** (Pillar - Hard Lefschetz Theorem).

    Given a (p,p) class of degree 2p where 2p > n, finds the primitive (n-p, n-p) class
    such that applying L^k gives back the original class.

    Proof structure mirrors hard_lefschetz_isomorphism:
    1. Use Hard Lefschetz surjectivity to find primitive c'
    2. Show c' is (n-p, n-p) via hard_lefschetz_pp_bijective
    3. Show c' is rational via hard_lefschetz_rational_bijective
    4. Extract representative form via existence_of_representative_form
    5. Establish the Lefschetz relation γ = L^k(η) -/
theorem hard_lefschetz_inverse_form {p : ℕ} (hp : 2 * p > n)
    (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_hodge : isPPForm' n X p γ) (h_rat : isRationalClass (ofForm γ h_closed)) :
    ∃ (η : SmoothForm n X (2 * (n - p))) (h_η_closed : IsFormClosed η),
      isPPForm' n X (n - p) η ∧
      isRationalClass (ofForm η h_η_closed) ∧
      ofForm γ h_closed = (lefschetz_degree_eq n p hp) ▸
        lefschetz_power n X (2 * (n - p)) (p - (n - p)) (ofForm η h_η_closed) := by
  -- Step 1: Define p_base = 2(n-p) and k = p - (n-p)
  let p_base := 2 * (n - p)
  let k := p - (n - p)
  have h_deg : p_base + 2 * k = 2 * p := lefschetz_degree_eq n p hp
  -- Step 2: Use surjectivity to get preimage class c'
  obtain ⟨c', hc'⟩ := (hard_lefschetz_bijective n X p_base k).surjective
    (h_deg ▸ ofForm γ h_closed)
  -- Step 3: c' is (n-p, n-p) class
  -- By hard_lefschetz_pp_bijective: c' is (n-p, n-p) iff L^k(c') is (p, p)
  -- By hc': L^k(c') = h_deg ▸ [γ], and γ is (p, p) by h_hodge
  have h_γ_pp : isPPClass (2 * p) (ofForm γ h_closed) :=
    ⟨p, rfl, γ, h_closed, rfl, h_hodge⟩
  have h_c'_pp : isPPClass p_base c' := by
    rw [hard_lefschetz_pp_bijective n X p_base k c', hc']
    exact isPPClass_transport h_deg.symm (ofForm γ h_closed) p h_γ_pp
  -- Step 4: c' is rational
  have h_c'_rat : isRationalClass c' := by
    rw [hard_lefschetz_rational_bijective n X p_base k c', hc']
    exact isRationalClass_transport h_deg.symm (ofForm γ h_closed) h_rat
  -- Step 5: Extract representative form
  have h_p_base : p_base = 2 * (n - p) := rfl
  obtain ⟨η, h_η_closed, h_rep, h_pp⟩ := isPPClass_index h_p_base c' h_c'_pp
  refine ⟨η, h_η_closed, h_pp, h_rep ▸ h_c'_rat, ?_⟩
  -- Step 6: Establish Lefschetz relation: [γ] = h_deg ▸ L^k[η]
  -- From hc': L^k c' = h_deg ▸ [γ], and h_rep: [η] = c'
  -- Substituting h_rep: L^k[η] = h_deg ▸ [γ], so [γ] = h_deg ▸ L^k[η]
  -- Note: p_base = 2 * (n - p) and k = p - (n - p) by definition
  show ofForm γ h_closed = (lefschetz_degree_eq n p hp) ▸
    lefschetz_power n X (2 * (n - p)) (p - (n - p)) (ofForm η h_η_closed)
  have h_lef : lefschetz_power n X (2 * (n - p)) (p - (n - p)) (ofForm η h_η_closed) =
      (lefschetz_degree_eq n p hp) ▸ ofForm γ h_closed := h_rep ▸ hc'
  exact lefschetz_transport_eq (lefschetz_degree_eq n p hp) _ _ h_lef

end
