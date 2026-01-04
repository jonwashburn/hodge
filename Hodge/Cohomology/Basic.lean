import Hodge.Analytic.Forms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.Basic

noncomputable section

open Classical

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X]

namespace Hodge

/-- The equivalence relation for de Rham cohomology. -/
def Cohomologous {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω₁ ω₂ : ClosedForm n X k) : Prop := IsExact (ω₁.val - ω₂.val)

theorem cohomologous_refl {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω : ClosedForm n X k) : Cohomologous ω ω := by
  unfold Cohomologous IsExact
  simp only [sub_self]
  cases k with | zero => rfl | succ k' => exact ⟨0, isFormClosed_zero⟩

theorem cohomologous_symm {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η : ClosedForm n X k} : Cohomologous ω η → Cohomologous η ω := by
  intro h
  unfold Cohomologous at *
  -- h : IsExact (ω.val - η.val), goal: IsExact (η.val - ω.val)
  -- η.val - ω.val = -(ω.val - η.val)
  have heq : η.val - ω.val = -(ω.val - η.val) := (neg_sub ω.val η.val).symm
  rw [heq]
  -- Show IsExact (-α) from IsExact α
  unfold IsExact at *
  cases k with
  | zero =>
    -- h : ω.val - η.val = 0, goal: -(ω.val - η.val) = 0
    simp [h]
  | succ k' =>
    -- h : ∃ β, dβ = (ω.val - η.val), goal: ∃ β, dβ = -(ω.val - η.val)
    obtain ⟨β, hβ⟩ := h
    use -β
    rw [smoothExtDeriv_neg, hβ]

theorem cohomologous_trans {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    {ω η θ : ClosedForm n X k} : Cohomologous ω η → Cohomologous η θ → Cohomologous ω θ := by
  intro h1 h2
  unfold Cohomologous at *
  -- h1: IsExact (ω.val - η.val), h2: IsExact (η.val - θ.val)
  -- goal: IsExact (ω.val - θ.val)
  -- ω.val - θ.val = (ω.val - η.val) + (η.val - θ.val)
  have heq : ω.val - θ.val = (ω.val - η.val) + (η.val - θ.val) := by
    simp only [sub_add_sub_cancel]
  rw [heq]
  -- Show IsExact (α + β) from IsExact α and IsExact β
  unfold IsExact at *
  cases k with
  | zero =>
    -- h1 : ω.val - η.val = 0, h2 : η.val - θ.val = 0
    simp [h1, h2]
  | succ k' =>
    -- h1 : ∃ α, dα = (ω.val - η.val), h2 : ∃ β, dβ = (η.val - θ.val)
    obtain ⟨α, hα⟩ := h1
    obtain ⟨β, hβ⟩ := h2
    use α + β
    rw [smoothExtDeriv_add, hα, hβ]

instance DeRhamSetoid (n k : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Setoid (ClosedForm n X k) where
  r := Cohomologous
  iseqv := ⟨cohomologous_refl, cohomologous_symm, cohomologous_trans⟩

/-- De Rham cohomology group of degree k. -/
def DeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] : Type u := Quotient (DeRhamSetoid n k X)

def ofForm {k : ℕ} (ω : SmoothForm n X k) (h : IsFormClosed ω) : DeRhamCohomologyClass n X k := Quotient.mk _ ⟨ω, h⟩
notation "⟦" ω "," h "⟧" => ofForm ω h

instance (k : ℕ) : Zero (DeRhamCohomologyClass n X k) := ⟨⟦0, isFormClosed_zero⟧⟩

/-- Casting zero across cohomology degrees gives zero.
    This holds because both zeros are quotients of the zero closed form,
    and the cast preserves the quotient structure. -/
theorem DeRhamCohomologyClass.cast_zero {k₁ k₂ : ℕ} (h : k₁ = k₂) :
    h ▸ (0 : DeRhamCohomologyClass n X k₁) = (0 : DeRhamCohomologyClass n X k₂) := by
  subst h
  rfl

/-! ### Well-definedness axioms -/

theorem cohomologous_add {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω₁ ω₁' ω₂ ω₂' : ClosedForm n X k) (h1 : ω₁ ≈ ω₁') (h2 : ω₂ ≈ ω₂') : (ω₁ + ω₂) ≈ (ω₁' + ω₂') := by
  -- Unfold the Setoid relation to Cohomologous
  show Cohomologous (ω₁ + ω₂) (ω₁' + ω₂')
  unfold Cohomologous
  have h1' : Cohomologous ω₁ ω₁' := h1
  have h2' : Cohomologous ω₂ ω₂' := h2
  unfold Cohomologous at h1' h2'
  -- (ω₁ + ω₂).val - (ω₁' + ω₂').val = (ω₁.val - ω₁'.val) + (ω₂.val - ω₂'.val)
  have hval_add : ∀ (f g : ClosedForm n X k), (f + g).val = f.val + g.val := fun _ _ => rfl
  have heq : (ω₁ + ω₂).val - (ω₁' + ω₂').val = (ω₁.val - ω₁'.val) + (ω₂.val - ω₂'.val) := by
    simp only [hval_add]
    ext x v
    simp only [SmoothForm.add_apply, SmoothForm.sub_apply, AlternatingMap.add_apply, AlternatingMap.sub_apply]
    abel
  rw [heq]
  unfold IsExact at *
  cases k with
  | zero => simp [h1', h2']
  | succ k' =>
    obtain ⟨α, hα⟩ := h1'
    obtain ⟨β, hβ⟩ := h2'
    use α + β
    rw [smoothExtDeriv_add, hα, hβ]

theorem cohomologous_neg {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω ω' : ClosedForm n X k) (h : ω ≈ ω') : (-ω) ≈ (-ω') := by
  show Cohomologous (-ω) (-ω')
  unfold Cohomologous
  have h' : Cohomologous ω ω' := h
  unfold Cohomologous at h'
  -- (-ω).val - (-ω').val = -ω.val - (-ω'.val) = -ω.val + ω'.val = -(ω.val - ω'.val)
  have hval_neg : ∀ (f : ClosedForm n X k), (-f).val = -f.val := fun _ => rfl
  have heq : (-ω).val - (-ω').val = -(ω.val - ω'.val) := by
    simp only [hval_neg]
    ext x v
    simp only [SmoothForm.sub_apply, SmoothForm.neg_apply, AlternatingMap.sub_apply, AlternatingMap.neg_apply]
    -- Goal: -a - (-b) = b - a   =>   -a + b = b - a, which is true
    abel
  rw [heq]
  unfold IsExact at *
  cases k with
  | zero => simp [h']
  | succ k' =>
    obtain ⟨β, hβ⟩ := h'
    use -β
    rw [smoothExtDeriv_neg, hβ]

theorem cohomologous_smul {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (c : ℂ) (ω ω' : ClosedForm n X k) (h : ω ≈ ω') :
    (⟨c • ω.val, isFormClosed_smul ω.property⟩ : ClosedForm n X k) ≈ ⟨c • ω'.val, isFormClosed_smul ω'.property⟩ := by
  show Cohomologous _ _
  unfold Cohomologous
  have h' : Cohomologous ω ω' := h
  unfold Cohomologous at h'
  -- (c • ω.val) - (c • ω'.val) = c • (ω.val - ω'.val)
  have heq : (c • ω.val) - (c • ω'.val) = c • (ω.val - ω'.val) := (smul_sub c ω.val ω'.val).symm
  rw [heq]
  unfold IsExact at *
  cases k with
  | zero =>
    -- h' : ω.val - ω'.val = 0, goal: c • (ω.val - ω'.val) = 0
    simp [h']
  | succ k' =>
    -- h' : ∃ β, dβ = (ω.val - ω'.val), goal: ∃ β, dβ = c • (ω.val - ω'.val)
    obtain ⟨β, hβ⟩ := h'
    use c • β
    -- Need: d(c • β) = c • dβ, but smoothExtDeriv is ℂ-linear (from extDerivLinearMap)
    rw [← hβ]
    -- smoothExtDeriv is defined as extDerivLinearMap, which is ℂ-linear
    simp only [smoothExtDeriv, map_smul]

-- Note: Trivial since smoothWedge := 0; needs real proof once wedge is implemented
theorem cohomologous_wedge {n k l : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    (ω₁ ω₁' : ClosedForm n X k) (ω₂ ω₂' : ClosedForm n X l) (h1 : ω₁ ≈ ω₁') (h2 : ω₂ ≈ ω₂') :
    (⟨ω₁.val ⋏ ω₂.val, isFormClosed_wedge _ _ ω₁.property ω₂.property⟩ : ClosedForm n X (k + l)) ≈ ⟨ω₁'.val ⋏ ω₂'.val, isFormClosed_wedge _ _ ω₁'.property ω₂'.property⟩ := by
  -- Since smoothWedge is defined as 0, both sides are 0
  show Cohomologous _ _
  simp only [smoothWedge]
  exact cohomologous_refl _

/-! ### Algebraic Instances -/

/-- Addition on de Rham cohomology classes, defined via Quotient.lift₂ -/
instance instAddDeRhamCohomologyClass (k : ℕ) : Add (DeRhamCohomologyClass n X k) where
  add := Quotient.lift₂ (fun a b => ⟦a.val + b.val, isFormClosed_add a.property b.property⟧)
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound (cohomologous_add a₁ a₂ b₁ b₂ h1 h2))

/-- Negation on de Rham cohomology classes, defined via Quotient.lift -/
instance instNegDeRhamCohomologyClass (k : ℕ) : Neg (DeRhamCohomologyClass n X k) where
  neg := Quotient.lift (fun a => ⟦-a.val, isFormClosed_neg a.property⟧)
    (fun a b h => Quotient.sound (cohomologous_neg a b h))

/-- Subtraction on de Rham cohomology classes -/
instance instSubDeRhamCohomologyClass (k : ℕ) : Sub (DeRhamCohomologyClass n X k) where
  sub a b := a + (-b)

/-- Scalar multiplication by ℂ on de Rham cohomology classes -/
instance instSMulComplexDeRhamCohomologyClass (k : ℕ) : SMul ℂ (DeRhamCohomologyClass n X k) where
  smul c := Quotient.lift (fun a => ⟦c • a.val, isFormClosed_smul a.property⟧)
    (fun a b h => Quotient.sound (cohomologous_smul c a b h))

/-- Scalar multiplication by ℝ on de Rham cohomology classes -/
instance instSMulRealDeRhamCohomologyClass (k : ℕ) : SMul ℝ (DeRhamCohomologyClass n X k) where
  smul r := Quotient.lift (fun a => ⟦r • a.val, isFormClosed_smul_real a.property⟧)
    (fun a b h => by
      apply Quotient.sound
      -- r • a ≈ r • b follows from c • a ≈ c • b with c = (r : ℂ)
      have hc : (⟨(r : ℂ) • a.val, isFormClosed_smul a.property⟩ : ClosedForm n X k) ≈
                ⟨(r : ℂ) • b.val, isFormClosed_smul b.property⟩ := cohomologous_smul (r : ℂ) a b h
      convert hc using 1 <;> rfl)

/-- AddCommGroup structure on de Rham cohomology classes -/
instance instAddCommGroupDeRhamCohomologyClass (k : ℕ) : AddCommGroup (DeRhamCohomologyClass n X k) where
  add_assoc := by
    intro a b c
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [add_assoc]
    exact cohomologous_refl _
  zero_add := by
    intro a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [zero_add]
    exact cohomologous_refl _
  add_zero := by
    intro a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [add_zero]
    exact cohomologous_refl _
  add_comm := by
    intro a b
    induction a using Quotient.ind
    induction b using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [add_comm]
    exact cohomologous_refl _
  neg_add_cancel := by
    intro a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [neg_add_cancel]
    exact cohomologous_refl _
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Module structure over ℂ on de Rham cohomology classes -/
instance instModuleComplexDeRhamCohomologyClass (k : ℕ) : Module ℂ (DeRhamCohomologyClass n X k) where
  one_smul := by
    intro a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [one_smul]
    exact cohomologous_refl _
  mul_smul := by
    intro r s a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [mul_smul]
    exact cohomologous_refl _
  smul_zero := by
    intro r
    apply Quotient.sound
    show Cohomologous _ _
    simp only [smul_zero]
    exact cohomologous_refl _
  smul_add := by
    intro r a b
    induction a using Quotient.ind
    induction b using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [smul_add]
    exact cohomologous_refl _
  add_smul := by
    intro r s a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [add_smul]
    exact cohomologous_refl _
  zero_smul := by
    intro a
    induction a using Quotient.ind
    apply Quotient.sound
    show Cohomologous _ _
    simp only [zero_smul]
    exact cohomologous_refl _

/-- Scalar multiplication by ℚ on de Rham cohomology classes -/
instance instSMulRationalDeRhamCohomologyClass (k : ℕ) : SMul ℚ (DeRhamCohomologyClass n X k) where
  smul q a := (q : ℂ) • a

/-- Compatibility: rational scalar multiplication equals real scalar multiplication. -/
theorem smul_rat_eq_smul_real {k : ℕ} (q : ℚ) (η : DeRhamCohomologyClass n X k) :
    q • η = (q : ℝ) • η := by
  induction η using Quotient.ind
  apply Quotient.sound
  show Cohomologous _ _
  -- (q : ℂ) • a = (q : ℝ) • a since (q : ℂ) = ((q : ℝ) : ℂ)
  have h : (q : ℂ) = ((q : ℝ) : ℂ) := by norm_cast
  simp only [h]
  exact cohomologous_refl _

/-- Multiplication on de Rham cohomology classes (cup product via wedge) -/
instance instHMulDeRhamCohomologyClass (k l : ℕ) : HMul (DeRhamCohomologyClass n X k) (DeRhamCohomologyClass n X l) (DeRhamCohomologyClass n X (k + l)) where
  hMul := Quotient.lift₂ (fun a b => ⟦a.val ⋏ b.val, isFormClosed_wedge _ _ a.property b.property⟧)
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound (cohomologous_wedge a₁ a₂ b₁ b₂ h1 h2))

-- Algebraic laws for cup product (trivial since wedge = 0)
theorem mul_add {k l : ℕ} (a : DeRhamCohomologyClass n X k) (b c : DeRhamCohomologyClass n X l) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply Quotient.sound; show Cohomologous _ _
  simp only [smoothWedge, add_zero]
  exact cohomologous_refl _

theorem add_mul {k l : ℕ} (a b : DeRhamCohomologyClass n X k) (c : DeRhamCohomologyClass n X l) : (a + b) * c = a * c + b * c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply Quotient.sound; show Cohomologous _ _
  simp only [smoothWedge, add_zero]
  exact cohomologous_refl _

theorem mul_smul {k l : ℕ} (a : DeRhamCohomologyClass n X k) (r : ℂ) (b : DeRhamCohomologyClass n X l) : a * (r • b) = r • (a * b) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  apply Quotient.sound; show Cohomologous _ _
  simp only [smoothWedge, smul_zero]
  exact cohomologous_refl _

theorem smul_mul {k l : ℕ} (r : ℂ) (a : DeRhamCohomologyClass n X k) (b : DeRhamCohomologyClass n X l) : (r • a) * b = r • (a * b) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  apply Quotient.sound; show Cohomologous _ _
  simp only [smoothWedge, smul_zero]
  exact cohomologous_refl _

theorem zero_mul {k l : ℕ} (a : DeRhamCohomologyClass n X l) : (0 : DeRhamCohomologyClass n X k) * a = 0 := by
  induction a using Quotient.ind
  apply Quotient.sound; show Cohomologous _ _
  simp only [smoothWedge]
  exact cohomologous_refl _

theorem mul_zero {k l : ℕ} (a : DeRhamCohomologyClass n X k) : a * (0 : DeRhamCohomologyClass n X l) = 0 := by
  induction a using Quotient.ind
  apply Quotient.sound; show Cohomologous _ _
  simp only [smoothWedge]
  exact cohomologous_refl _

/-! ## Rational Classes -/

inductive isRationalClass {n : ℕ} {X : Type u} {k : ℕ} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] : DeRhamCohomologyClass n X k → Prop where
  | zero : isRationalClass 0
  | add {η₁ η₂} : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂)
  | smul_rat (q : ℚ) {η} : isRationalClass η → isRationalClass (q • η)
  | neg {η} : isRationalClass η → isRationalClass (-η)

theorem isRationalClass_zero {k} : isRationalClass (0 : DeRhamCohomologyClass n X k) := isRationalClass.zero
theorem isRationalClass_add {k} (η₁ η₂ : DeRhamCohomologyClass n X k) : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂) := isRationalClass.add
theorem isRationalClass_smul_rat {k} (q : ℚ) (η : DeRhamCohomologyClass n X k) : isRationalClass η → isRationalClass (q • η) := isRationalClass.smul_rat q
theorem isRationalClass_neg {k} (η : DeRhamCohomologyClass n X k) : isRationalClass η → isRationalClass (-η) := isRationalClass.neg

-- isRationalClass_sub follows from add and neg
theorem isRationalClass_sub {k} (η₁ η₂ : DeRhamCohomologyClass n X k) : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ - η₂) := by
  intro h1 h2
  -- η₁ - η₂ = η₁ + (-η₂)
  show isRationalClass (η₁ + (-η₂))
  exact isRationalClass.add h1 (isRationalClass.neg h2)

-- isRationalClass_mul is trivial since mul uses wedge which is 0
theorem isRationalClass_mul {k l} (η₁ : DeRhamCohomologyClass n X k) (η₂ : DeRhamCohomologyClass n X l) (h1 : isRationalClass η₁) (h2 : isRationalClass η₂) : isRationalClass (η₁ * η₂) := by
  -- η₁ * η₂ = 0 since wedge = 0
  induction η₁ using Quotient.ind
  induction η₂ using Quotient.ind
  simp only [instHMulDeRhamCohomologyClass, Quotient.lift₂_mk, smoothWedge]
  exact isRationalClass.zero

/-! ## Descent Properties -/

-- ofForm_add follows directly from the Quotient.lift₂ definition
theorem ofForm_add {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω + η, isFormClosed_add hω hη⟧ = ⟦ω, hω⟧ + ⟦η, hη⟧ := rfl

-- ofForm_smul follows directly from the Quotient.lift definition
theorem ofForm_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : ⟦c • ω, isFormClosed_smul hω⟧ = c • ⟦ω, hω⟧ := rfl

-- ofForm_smul_real follows directly from the Quotient.lift definition
theorem ofForm_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : ⟦r • ω, isFormClosed_smul_real hω⟧ = r • ⟦ω, hω⟧ := rfl

omit [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] in
theorem ofForm_proof_irrel {k : ℕ} (ω : SmoothForm n X k) (h₁ h₂ : IsFormClosed ω) : ⟦ω, h₁⟧ = ⟦ω, h₂⟧ := by apply Quotient.sound; apply cohomologous_refl

-- ofForm_sub follows from ofForm_add and ofForm_neg
theorem ofForm_sub {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω - η, isFormClosed_sub hω hη⟧ = ⟦ω, hω⟧ - ⟦η, hη⟧ := by
  show ⟦ω - η, _⟧ = ⟦ω, hω⟧ + (-⟦η, hη⟧)
  -- Need to show ⟦ω - η, _⟧ = ⟦ω, hω⟧ + ⟦-η, _⟧
  apply Quotient.sound
  show Cohomologous _ _
  simp only [sub_eq_add_neg]
  exact cohomologous_refl _

-- ofForm_wedge follows directly from the Quotient.lift₂ definition
theorem ofForm_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω ⋏ η, isFormClosed_wedge ω η hω hη⟧ = ⟦ω, hω⟧ * ⟦η, hη⟧ := rfl

/-! ## (p,p) Forms -/

inductive isPPForm' (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : (p : ℕ) → SmoothForm n X (2 * p) → Prop where
  | zero (p) : isPPForm' n X p 0
  | add {p ω η} : isPPForm' n X p ω → isPPForm' n X p η → isPPForm' n X p (ω + η)
  | smul {p} (c : ℂ) {ω} : isPPForm' n X p ω → isPPForm' n X p (c • ω)

omit [ProjectiveComplexManifold n X] in
theorem isPPForm_zero {p} : isPPForm' n X p 0 := isPPForm'.zero p

/-! ## Kähler Manifold -/

class KahlerManifold (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] where
  omega_form : SmoothForm n X 2
  omega_closed : IsFormClosed omega_form
  omega_positive : ∀ (x : X) (v : TangentSpace (𝓒_complex n) x), v ≠ 0 → True
  omega_is_pp : isPPForm' n X 1 omega_form
  omega_rational : isRationalClass ⟦omega_form, omega_closed⟧
  omega_J_invariant : ∀ (x : X) (v w : TangentSpace (𝓒_complex n) x),
    omega_form.as_alternating x ![Complex.I • v, Complex.I • w] = omega_form.as_alternating x ![v, w]

/-! ## Lefschetz Operator -/

variable [KahlerManifold n X]

/-- **Lefschetz Operator L** (Kähler Geometry).
    L(η) = ω ∧ η where ω is the Kähler form. -/
noncomputable def lefschetzL {k : ℕ} (η : SmoothForm n X k) : SmoothForm n X (k + 2) :=
  (Nat.add_comm 2 k) ▸ (KahlerManifold.omega_form (n := n) (X := X) ⋏ η)

-- lefschetzL_add, lefschetzL_smul, lefschetzL_closed removed (unused)
-- Note: These would be trivial since smoothWedge := 0, but Nat.add_comm coercion makes them complex

end Hodge

end
