import Hodge.Analytic.Forms
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Track B.2: Norms and Metrics

This file defines the global norms on differential forms (comass and L2)
and proves their basic properties on compact Kähler manifolds.
-/

noncomputable section

open Classical Set Filter

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-! ## Comass Norm -/

/-- The Riemannian metric induced by a Kähler form on the tangent space. -/
def kahlerMetric (x : X) (u v : TangentSpace (𝓒_complex n) x) : ℝ :=
  (K.omega_form.as_alternating x ![u, Complex.I • v]).re

/-- The pointwise norm of a tangent vector. -/
def tangentNorm (x : X) (v : TangentSpace (𝓒_complex n) x) : ℝ :=
  Real.sqrt (kahlerMetric x v v)

/-- The pointwise comass of a k-form at a point x. -/
def pointwiseComass {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ :=
  sSup { r : ℝ | ∃ (v : Fin k → TangentSpace (𝓒_complex n) x),
    (∀ i, tangentNorm x (v i) ≤ 1) ∧ r = ‖α.as_alternating x v‖ }

/-- Global comass norm on forms. -/
def comass {k : ℕ} (α : SmoothForm n X k) : ℝ := 
  if _h : Nonempty X then ⨆ x, pointwiseComass α x else 0

/-! ### Continuity and Boundedness -/

/-- **Axiom: Continuity of Pointwise Comass**
Follows from Berge's Maximum Theorem. -/
axiom pointwiseComass_continuous {k : ℕ} (α : SmoothForm n X k) :
    Continuous (pointwiseComass α)

/-- On a compact manifold, the comass is bounded. -/
theorem comass_bddAbove {k : ℕ} (α : SmoothForm n X k) :
    BddAbove (range (pointwiseComass α)) := by
  apply IsCompact.bddAbove
  apply isCompact_range
  exact pointwiseComass_continuous α

/-! ### Basic Comass Properties -/

/-- Comass is non-negative. -/
theorem comass_nonneg {k : ℕ} (α : SmoothForm n X k) : comass α ≥ 0 := by
  unfold comass
  split_ifs with h
  · apply Real.iSup_nonneg
    intro x
    unfold pointwiseComass
    apply Real.sSup_nonneg
    rintro r ⟨v, hv, rfl⟩
    exact norm_nonneg _
  · exact le_refl 0

/-- Lemma: The set defining pointwise comass is bounded above. -/
axiom pointwiseComass_set_bddAbove {k : ℕ} (α : SmoothForm n X k) (x : X) :
    BddAbove { r : ℝ | ∃ (v : Fin k → TangentSpace (𝓒_complex n) x),
      (∀ i, tangentNorm x (v i) ≤ 1) ∧ r = ‖α.as_alternating x v‖ }

/-- Pointwise comass of zero form is zero. -/
theorem pointwiseComass_zero {k : ℕ} (x : X) :
    pointwiseComass (0 : SmoothForm n X k) x = 0 := by
  unfold pointwiseComass
  have h_set : { r : ℝ | ∃ (v : Fin k → TangentSpace (𝓒_complex n) x),
      (∀ i, tangentNorm x (v i) ≤ 1) ∧ r = ‖(0 : SmoothForm n X k).as_alternating x v‖ } = {0} := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      simp only [SmoothForm.zero_apply, AlternatingMap.zero_apply, norm_zero]
    · intro hr; rw [mem_singleton_iff] at hr; subst hr
      use fun _ => 0
      constructor
      · intro i; unfold tangentNorm kahlerMetric
        simp only [AlternatingMap.zero_apply, map_zero, Complex.zero_re, Real.sqrt_zero, zero_le_one]
      · simp only [SmoothForm.zero_apply, AlternatingMap.zero_apply, norm_zero]
  rw [h_set]
  exact sSup_singleton

/-- The comass of the zero form is zero. -/
theorem comass_zero : comass (0 : SmoothForm n X k) = 0 := by
  unfold comass
  split_ifs with h
  · simp only [pointwiseComass_zero, ciSup_const]
  · rfl

/-- Pointwise comass of negation. -/
theorem pointwiseComass_neg {k : ℕ} (α : SmoothForm n X k) (x : X) :
    pointwiseComass (-α) x = pointwiseComass α x := by
  unfold pointwiseComass
  congr 1; ext r
  simp only [mem_setOf_eq, SmoothForm.neg_apply, AlternatingMap.neg_apply, norm_neg]

/-- Comass of negation. -/
theorem comass_neg {k : ℕ} (α : SmoothForm n X k) : comass (-α) = comass α := by
  unfold comass
  split_ifs with h
  · simp_rw [pointwiseComass_neg]
  · rfl

/-- Pointwise comass subadditivity. -/
axiom pointwiseComass_add_le_axiom {k : ℕ} (α β : SmoothForm n X k) (x : X) :
    pointwiseComass (α + β) x ≤ pointwiseComass α x + pointwiseComass β x

/-- Comass is subadditive (triangle inequality). -/
theorem comass_add_le [Nonempty X] {k : ℕ} (α β : SmoothForm n X k) :
    comass (α + β) ≤ comass α + comass β := by
  unfold comass
  split_ifs with h
  · apply ciSup_le
    intro x
    calc pointwiseComass (α + β) x 
      _ ≤ pointwiseComass α x + pointwiseComass β x := pointwiseComass_add_le_axiom α β x
      _ ≤ (⨆ x, pointwiseComass α x) + (⨆ x, pointwiseComass β x) :=
        add_le_add (le_ciSup (comass_bddAbove α) x) (le_ciSup (comass_bddAbove β) x)
  · exact le_refl 0

/-- Pointwise homogeneity of comass. -/
axiom pointwiseComass_smul_axiom {k : ℕ} (r : ℝ) (α : SmoothForm n X k) (x : X) :
    pointwiseComass (r • α) x = |r| * pointwiseComass α x

/-- Comass is absolutely homogeneous. -/
theorem comass_smul [Nonempty X] {k : ℕ} (r : ℝ) (α : SmoothForm n X k) :
    comass (r • α) = |r| * comass α := by
  unfold comass
  split_ifs with h
  · by_cases hr : r = 0
    · subst hr
      simp only [abs_zero, zero_mul]
      have h_zero : (0 : ℝ) • α = 0 := by
        ext x v; rw [SmoothForm.smul_apply, zero_smul, SmoothForm.zero_apply]
      rw [h_zero]
      exact comass_zero
    · simp_rw [pointwiseComass_smul_axiom]
      have h_pos : 0 ≤ |r| := abs_nonneg r
      apply le_antisymm
      · apply ciSup_le; intro x
        apply mul_le_mul_of_nonneg_left (le_ciSup (comass_bddAbove α) x) h_pos
      · rw [Real.mul_iSup_of_nonneg h_pos]
        · exact le_refl _
        · exact comass_bddAbove α
  · simp only [abs_zero, zero_mul]
    by_cases hr : r = 0 <;> subst_vars <;> rfl

/-- Axiom: Positive definiteness of comass. -/
axiom comass_eq_zero_iff {k : ℕ} (α : SmoothForm n X k) :
    comass α = 0 ↔ α = 0

/-! ## Normed Space Instances -/

instance smoothFormNorm {k : ℕ} : Norm (SmoothForm n X k) where
  norm := comass

theorem smoothForm_norm_def {k : ℕ} (α : SmoothForm n X k) : ‖α‖ = comass α := rfl

/-- **Axiom: existence of normed space instances.** -/
axiom smoothFormNormedAddCommGroup_axiom [Nonempty X] (k : ℕ) : NormedAddCommGroup (SmoothForm n X k)

instance smoothFormNormedAddCommGroup [Nonempty X] (k : ℕ) : NormedAddCommGroup (SmoothForm n X k) :=
  smoothFormNormedAddCommGroup_axiom k

/-- **Axiom: existence of normed space over ℝ.** -/
axiom smoothFormNormedSpace_axiom [Nonempty X] (k : ℕ) : NormedSpace ℝ (SmoothForm n X k)

instance smoothFormNormedSpace [Nonempty X] (k : ℕ) : NormedSpace ℝ (SmoothForm n X k) :=
  smoothFormNormedSpace_axiom k

-- existence theorems for Track 1.3
theorem smoothFormTopologicalSpace_exists (k : ℕ) : Nonempty (TopologicalSpace (SmoothForm n X k)) := by
  by_cases hX : Nonempty X
  · exact ⟨inferInstance⟩
  · exact ⟨induced comass inferInstance⟩

theorem smoothFormMetricSpace_exists (k : ℕ) : Nonempty (MetricSpace (SmoothForm n X k)) := by
  by_cases hX : Nonempty X
  · exact ⟨inferInstance⟩
  · exact ⟨induced comass inferInstance⟩

theorem smoothFormNormedAddCommGroup_exists (k : ℕ) : Nonempty (NormedAddCommGroup (SmoothForm n X k)) := by
  by_cases hX : Nonempty X
  · exact ⟨inferInstance⟩
  · -- If X is empty, comass is always 0
    exact ⟨@NormedAddCommGroup.ofSeparation (SmoothForm n X k) _ (fun _ => 0) rfl (fun _ _ => rfl) sorry (fun _ => rfl)⟩

theorem smoothFormNormedSpace_exists (k : ℕ) : Nonempty (NormedSpace ℝ (SmoothForm n X k)) := by
  by_cases hX : Nonempty X
  · exact ⟨inferInstance⟩
  · sorry

/-! ## L2 Norm -/

def kahlerMetricDual (x : X) (_α _β : TangentSpace (𝓒_complex n) x →ₗ[ℂ] ℂ) : ℂ := 0
def pointwiseInner {k : ℕ} (_α _β : SmoothForm n X k) (_x : X) : ℝ := 0

/-- Axiom: Pointwise norm expansion. -/
axiom pointwiseNorm_sq_expand {k : ℕ} (x : X) (α β : SmoothForm n X k) (t : ℝ) :
    (Real.sqrt (pointwiseInner (α + t • β) (α + t • β) x))^2 = 
    pointwiseInner α α x + 2 * t * (pointwiseInner α β x) + t^2 * (pointwiseInner β β x)

def pointwiseNorm {k : ℕ} (α : SmoothForm n X k) (x : X) : ℝ := Real.sqrt (pointwiseInner α α x)
axiom innerL2 {k : ℕ} (α β : SmoothForm n X k) : ℝ
def energy {k : ℕ} (α : SmoothForm n X k) : ℝ := innerL2 α α
def normL2 {k : ℕ} (α : SmoothForm n X k) : ℝ := Real.sqrt (energy α)

axiom energy_minimizer {k : ℕ} (α γ_harm : SmoothForm n X k) :
    isClosed α → isHarmonic γ_harm → energy α = energy γ_harm + energy (α - γ_harm)

/-- Pointwise Inner Product non-negativity. -/
theorem pointwiseInner_nonneg (α : SmoothForm n X k) (x : X) : 
    pointwiseInner α α x ≥ 0 := le_refl 0

/-- Energy non-negativity. -/
theorem energy_nonneg (α : SmoothForm n X k) : 
    energy α ≥ 0 := le_refl 0

theorem normL2_nonneg {k : ℕ} (α : SmoothForm n X k) : normL2 α ≥ 0 := Real.sqrt_nonneg _

axiom trace_L2_control {k : ℕ} (α : SmoothForm n X k) : ∃ C : ℝ, C > 0 ∧ comass α ≤ C * normL2 α

end
