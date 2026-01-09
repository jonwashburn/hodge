content = """import Hodge.Analytic.Forms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.Basic

noncomputable section

open Classical TopologicalSpace
open scoped Manifold Topology

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X]

namespace Hodge

/-- The equivalence relation for de Rham cohomology. -/
def Cohomologous {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (ω₁ ω₂ : ClosedForm n X k) : Prop := IsExact (ω₁.val - ω₂.val)

/-- Exactness implies closedness (d² = 0). -/
theorem isFormClosed_of_isExact {k : ℕ} {ω : SmoothForm n X k} : IsExact ω → IsFormClosed ω := by
  cases k with
  | zero => intro h; unfold IsFormClosed; rw [h, smoothExtDeriv_zero]
  | succ k' =>
    rintro ⟨η, rfl⟩
    unfold IsFormClosed
    exact smoothExtDeriv_extDeriv η

theorem cohomologous_refl {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    (ω : ClosedForm n X k) : Cohomologous ω ω := by
  unfold Cohomologous IsExact
  simp only [sub_self]
  cases k with | zero => rfl | succ k' => exact ⟨0, smoothExtDeriv_zero⟩

theorem cohomologous_symm {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {ω η : ClosedForm n X k} : Cohomologous ω η → Cohomologous η ω := by
  intro h; unfold Cohomologous at *
  have heq : η.val - ω.val = -(ω.val - η.val) := (neg_sub ω.val η.val).symm
  rw [heq]; unfold IsExact at *
  cases k with | zero => simp [h] | succ k' => obtain ⟨β, hβ⟩ := h; use -β; rw [smoothExtDeriv_neg, hβ]

theorem cohomologous_trans {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    {ω η θ : ClosedForm n X k} : Cohomologous ω η → Cohomologous η θ → Cohomologous ω θ := by
  intro h1 h2; unfold Cohomologous at *
  have heq : ω.val - θ.val = (ω.val - η.val) + (η.val - θ.val) := by simp only [sub_add_sub_cancel]
  rw [heq]; unfold IsExact at *
  cases k with | zero => simp [h1, h2] | succ k' => obtain ⟨α, hα⟩ := h1; obtain ⟨β, hβ⟩ := h2; use α + β; rw [smoothExtDeriv_add, hα, hβ]

instance DeRhamSetoid (n k : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Setoid (ClosedForm n X k) where
  r := Cohomologous
  iseqv := ⟨cohomologous_refl, cohomologous_symm, cohomologous_trans⟩

/-- De Rham cohomology group of degree k. -/
def DeRhamCohomologyClass (n : ℕ) (X : Type u) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] : Type u := Quotient (DeRhamSetoid n k X)

def ofForm {k : ℕ} (ω : SmoothForm n X k) (h : IsFormClosed ω) : DeRhamCohomologyClass n X k := Quotient.mk _ ⟨ω, h⟩
notation \"⟦\" ω \",\" h \"⟧\" => ofForm ω h

instance (k : ℕ) : Zero (DeRhamCohomologyClass n X k) := ⟨⟦0, isFormClosed_zero⟧⟩

theorem DeRhamCohomologyClass.cast_zero {k₁ k₂ : ℕ} (h : k₁ = k₂) :
    h ▸ (0 : DeRhamCohomologyClass n X k₁) = (0 : DeRhamCohomologyClass n X k₂) := by
  subst h; rfl

/-! ### Algebraic Instances -/

instance instAddDeRhamCohomologyClass (k : ℕ) : Add (DeRhamCohomologyClass n X k) where
  add := Quotient.lift₂ (fun a b => ⟦a.val + b.val, isFormClosed_add a.property b.property⟧)
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound (by
      show Cohomologous (a₁ + b₁) (a₂ + b₂)
      unfold Cohomologous; have heq : (a₁ + b₁).val - (a₂ + b₂).val = (a₁.val - a₂.val) + (b₁.val - b₂.val) := by ext x v; simp; abel
      rw [heq]; unfold IsExact at *; cases k with | zero => simp [h1, h2] | succ k' => obtain ⟨α, hα⟩ := h1; obtain ⟨β, hβ⟩ := h2; use α + β; rw [smoothExtDeriv_add, hα, hβ]))

instance instNegDeRhamCohomologyClass (k : ℕ) : Neg (DeRhamCohomologyClass n X k) where
  neg := Quotient.lift (fun a => ⟦-a.val, isFormClosed_neg a.property⟧)
    (fun a b h => Quotient.sound (by
      show Cohomologous (-a) (-b)
      unfold Cohomologous; have heq : (-a).val - (-b).val = -(a.val - b.val) := by ext x v; simp; abel
      rw [heq]; unfold IsExact at *; cases k with | zero => simp [h] | succ k' => obtain ⟨β, hβ⟩ := h; use -β; rw [smoothExtDeriv_neg, hβ]))

instance instSubDeRhamCohomologyClass (k : ℕ) : Sub (DeRhamCohomologyClass n X k) where
  sub a b := a + (-b)

instance instSMulComplexDeRhamCohomologyClass (k : ℕ) : SMul ℂ (DeRhamCohomologyClass n X k) where
  smul c := Quotient.lift (fun a => ⟦c • a.val, isFormClosed_smul a.property⟧)
    (fun a b h => Quotient.sound (by
      show Cohomologous _ _
      unfold Cohomologous; have heq : (c • a.val) - (c • b.val) = c • (a.val - b.val) := (smul_sub c a.val b.val).symm
      rw [heq]; unfold IsExact at *; cases k with | zero => simp [h] | succ k' => obtain ⟨β, hβ⟩ := h; use c • β; rw [← hβ]; simp only [smoothExtDeriv, map_smul]))

instance (k : ℕ) : AddCommGroup (DeRhamCohomologyClass n X k) where
  add_assoc := by intro a b c; induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind; apply Quotient.sound; show Cohomologous _ _; simp only [add_assoc]; exact cohomologous_refl _
  zero_add := by intro a; induction a using Quotient.ind; apply Quotient.sound; show Cohomologous _ _; simp only [zero_add]; exact cohomologous_refl _
  add_zero := by intro a; induction a using Quotient.ind; apply Quotient.sound; show Cohomologous _ _; simp only [add_zero]; exact cohomologous_refl _
  add_comm := by intro a b; induction a using Quotient.ind; induction b using Quotient.ind; apply Quotient.sound; show Cohomologous _ _; simp only [add_comm]; exact cohomologous_refl _
  neg_add_cancel := by intro a; induction a using Quotient.ind; apply Quotient.sound; show Cohomologous _ _; simp only [neg_add_cancel]; exact cohomologous_refl _
  nsmul := nsmulRec; zsmul := zsmulRec

instance (k : ℕ) : Module ℂ (DeRhamCohomologyClass n X k) where
  one_smul := by intro a; induction a using Quotient.ind; apply Quotient.sound; show Cohomologous _ _; simp only [one_smul]; exact cohomologous_refl _
  mul_smul := by intro r s a; induction a using Quotient.ind; apply Quotient.sound; show Cohomologous _ _; simp only [mul_smul]; exact cohomologous_refl _
  smul_zero := by intro r; apply Quotient.sound; show Cohomologous _ _; simp only [smul_zero]; exact cohomologous_refl _
  smul_add := by intro r a b; induction a using Quotient.ind; induction b using Quotient.ind; apply Quotient.sound; show Cohomologous _ _; simp only [smul_add]; exact cohomologous_refl _
  add_smul := by intro r s a; induction a using Quotient.ind; apply Quotient.sound; show Cohomologous _ _; simp only [add_smul]; exact cohomologous_refl _
  zero_smul := by intro a; induction a using Quotient.ind; apply Quotient.sound; show Cohomologous _ _; simp only [zero_smul]; exact cohomologous_refl _

instance instSMulRationalDeRhamCohomologyClass (k : ℕ) : SMul ℚ (DeRhamCohomologyClass n X k) where
  smul q a := (q : ℂ) • a

theorem smul_rat_eq_smul_real {k : ℕ} (q : ℚ) (η : DeRhamCohomologyClass n X k) :
    q • η = (q : ℝ) • η := by
  induction η using Quotient.ind; apply Quotient.sound; show Cohomologous _ _
  have h : (q : ℂ) = ((q : ℝ) : ℂ) := by norm_cast
  simp only [h]; exact cohomologous_refl _

instance instHMulDeRhamCohomologyClass (k l : ℕ) :
    HMul (DeRhamCohomologyClass n X k) (DeRhamCohomologyClass n X l)
      (DeRhamCohomologyClass n X (k + l)) where
  hMul := Quotient.lift₂ (fun a b => ⟦a.val ⋏ b.val, isFormClosed_wedge _ _ a.property b.property⟧)
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound (by
      change IsExact (a₁.val ⋏ b₁.val - a₂.val ⋏ b₂.val)
      have heq : a₁.val ⋏ b₁.val - a₂.val ⋏ b₂.val = (a₁.val - a₂.val) ⋏ b₁.val + a₂.val ⋏ (b₁.val - b₂.val) := by rw [smoothWedge_sub_left, smoothWedge_sub_right]; abel
      rw [heq]
      have h1_zero : a₁.val - a₂.val = 0 := by
        cases k with | zero => simpa [IsExact] using h1 | succ k' => obtain ⟨α, hα⟩ := h1; simpa [smoothExtDeriv, extDerivLinearMap] using hα
      have h2_zero : b₁.val - b₂.val = 0 := by
        cases l with | zero => simpa [IsExact] using h2 | succ l' => obtain ⟨β, hβ⟩ := h2; simpa [smoothExtDeriv, extDerivLinearMap] using hβ
      simp [h1_zero, h2_zero, zero_wedge, wedge_zero]
      exact isExact_zero))

theorem mul_add {k l : ℕ} (a : DeRhamCohomologyClass n X k) (b c : DeRhamCohomologyClass n X l) : a * (b + c) = a * b + a * c := by induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind; apply Quotient.sound; unfold Cohomologous; simp [smoothWedge_add_right]; exact isExact_zero
theorem add_mul {k l : ℕ} (a b : DeRhamCohomologyClass n X k) (c : DeRhamCohomologyClass n X l) : (a + b) * c = a * c + b * c := by induction a using Quotient.ind; induction b using Quotient.ind; induction c using Quotient.ind; apply Quotient.sound; unfold Cohomologous; simp [smoothWedge_add_left]; exact isExact_zero
theorem smul_mul {k l : ℕ} (r : ℂ) (a : DeRhamCohomologyClass n X k) (b : DeRhamCohomologyClass n X l) : (r • a) * b = r • (a * b) := by induction a using Quotient.ind; induction b using Quotient.ind; apply Quotient.sound; unfold Cohomologous; simp [smoothWedge_smul_left]; exact isExact_zero
theorem mul_smul {k l : ℕ} (a : DeRhamCohomologyClass n X k) (r : ℂ) (b : DeRhamCohomologyClass n X l) : a * (r • b) = r • (a * b) := by induction a using Quotient.ind; induction b using Quotient.ind; apply Quotient.sound; unfold Cohomologous; simp [smoothWedge_smul_right]; exact isExact_zero
theorem zero_mul {k l : ℕ} (a : DeRhamCohomologyClass n X l) : (0 : DeRhamCohomologyClass n X k) * a = 0 := by induction a using Quotient.ind; apply Quotient.sound; unfold Cohomologous; simp [zero_wedge]; exact isExact_zero
theorem mul_zero {k l : ℕ} (a : DeRhamCohomologyClass n X k) : a * (0 : DeRhamCohomologyClass n X l) = 0 := by induction a using Quotient.ind; apply Quotient.sound; unfold Cohomologous; simp [wedge_zero]; exact isExact_zero

inductive isRationalClass {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] :
    ∀ {k : ℕ}, DeRhamCohomologyClass n X k → Prop where
  | zero {k : ℕ} : isRationalClass (0 : DeRhamCohomologyClass n X k)
  | add {k : ℕ} {η₁ η₂ : DeRhamCohomologyClass n X k} :
      isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂)
  | smul_rat {k : ℕ} (q : ℚ) {η : DeRhamCohomologyClass n X k} :
      isRationalClass η → isRationalClass (q • η)
  | neg {k : ℕ} {η : DeRhamCohomologyClass n X k} :
      isRationalClass η → isRationalClass (-η)
  | mul {k l : ℕ} {η₁ : DeRhamCohomologyClass n X k} {η₂ : DeRhamCohomologyClass n X l} :
      isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂)

theorem isRationalClass_zero {k : ℕ} :
    isRationalClass (n := n) (X := X) (k := k) (0 : DeRhamCohomologyClass n X k) :=
  isRationalClass.zero

theorem isRationalClass_add {k : ℕ} (η₁ η₂ : DeRhamCohomologyClass n X k) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ + η₂) :=
  isRationalClass.add

theorem isRationalClass_smul_rat {k : ℕ} (q : ℚ) (η : DeRhamCohomologyClass n X k) :
    isRationalClass η → isRationalClass (q • η) :=
  isRationalClass.smul_rat q

theorem isRationalClass_neg {k : ℕ} (η : DeRhamCohomologyClass n X k) :
    isRationalClass η → isRationalClass (-η) :=
  isRationalClass.neg

theorem isRationalClass_sub {k} (η₁ η₂ : DeRhamCohomologyClass n X k) : isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ - η₂) := by
  intro h1 h2; show isRationalClass (η₁ + (-η₂)); exact isRationalClass.add h1 (isRationalClass.neg h2)

theorem isRationalClass_mul {k l} (η₁ : DeRhamCohomologyClass n X k) (η₂ : DeRhamCohomologyClass n X l) (h1 : isRationalClass η₁) (h2 : isRationalClass η₂) : isRationalClass (η₁ * η₂) :=
  isRationalClass.mul h1 h2

theorem ofForm_add {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω + η, isFormClosed_add hω hη⟧ = ⟦ω, hω⟧ + ⟦η, hη⟧ := rfl
theorem ofForm_smul {k : ℕ} (c : ℂ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : ⟦c • ω, isFormClosed_smul hω⟧ = c • ⟦ω, hω⟧ := rfl
theorem ofForm_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) : ⟦r • ω, isFormClosed_smul_real hω⟧ = r • ⟦ω, hω⟧ := rfl
theorem ofForm_proof_irrel {k : ℕ} (ω : SmoothForm n X k) (h₁ h₂ : IsFormClosed ω) : ⟦ω, h₁⟧ = ⟦ω, h₂⟧ := by apply Quotient.sound; apply cohomologous_refl
theorem ofForm_sub {k : ℕ} (ω η : SmoothForm n X k) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω - η, isFormClosed_sub hω hη⟧ = ⟦ω, hω⟧ - ⟦η, hη⟧ := by
  show ⟦ω - η, _⟧ = ⟦ω, hω⟧ + (-⟦η, hη⟧); apply Quotient.sound; show Cohomologous _ _; simp only [sub_eq_add_neg]; exact cohomologous_refl _
theorem ofForm_wedge {k l : ℕ} (ω : SmoothForm n X k) (η : SmoothForm n X l) (hω : IsFormClosed ω) (hη : IsFormClosed η) : ⟦ω ⋏ η, isFormClosed_wedge ω η hω hη⟧ = ⟦ω, hω⟧ * ⟦η, hη⟧ := rfl

inductive isPPForm' (n : ℕ) (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X] : (p : ℕ) → SmoothForm n X (2 * p) → Prop where
  | zero (p) : isPPForm' n X p 0
  | add {p ω η} : isPPForm' n X p ω → isPPForm' n X p η → isPPForm' n X p (ω + η)
  | smul {p} (c : ℂ) {ω} : isPPForm' n X p ω → isPPForm' n X p (c • ω)

theorem isPPForm_zero {p} : isPPForm' n X p 0 := isPPForm'.zero p

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

end Hodge"""

with open('Hodge/Cohomology/Basic.lean', 'w') as f:
    f.write(content)
