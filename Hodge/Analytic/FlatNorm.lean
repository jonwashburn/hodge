import Hodge.Analytic.Currents
import Hodge.Analytic.Norms
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!

This file defines the flat norm on currents and proves its basic properties.
The flat norm is the natural metric for the space of integral currents.
-/

noncomputable section

open Classical Set

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-- **The Flat Norm** (Federer-Fleming, 1960).
    The flat norm of a current T is the infimum of M(S) + M(V) such that T = S + ∂V.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
def flatNorm {k : ℕ} (T : Current n X k) : ℝ :=
  sInf { r | ∃ (S : Current n X k) (V : Current n X (k + 1)),
    T = S + Current.boundary V ∧ Current.mass S + Current.mass V = r }

/-- The flat norm is non-negative. -/
theorem flatNorm_nonneg {k : ℕ} (T : Current n X k) : flatNorm T ≥ 0 := by
  apply Real.sInf_nonneg
  rintro r ⟨S, V, _, hr⟩
  rw [← hr]
  apply add_nonneg <;> apply Current.mass_nonneg

/-- The flat norm of the zero current is zero. -/
theorem flatNorm_zero {k : ℕ} : flatNorm (0 : Current n X k) = 0 := by
  apply le_antisymm
  · apply sInf_le
    use 0, 0
    constructor
    · ext ω; simp [Current.boundary, Current.add_curr, Current.zero]
    · simp [Current.mass_zero]
  · apply flatNorm_nonneg

/-- Bound evaluation by mass. -/
theorem eval_le_mass {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ Current.mass T * comass ψ := by
  if h : comass ψ = 0 then
    have h_ψ : ψ = 0 := (comass_eq_zero_iff (n := n) (X := X) (k := k) ψ).mp h
    have hT0 : T.toFun 0 = 0 := by
      have h := T.is_linear 0 0 0
      simp at h; exact h
    rw [h_ψ, hT0]
    simp [Current.mass_nonneg]
  else
    let r := comass ψ
    let ψ' := (1 / r) • ψ
    have hr : 0 < r := lt_of_le_of_ne (comass_nonneg ψ) (ne_comm.mp h)
    have hcom : comass ψ' = 1 := by
      rw [comass_smul, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel (ne_of_gt hr)]
    have : |T.toFun ψ'| ≤ Current.mass T := by
      apply le_sSup
      · obtain ⟨M, hM⟩ := T.is_bounded
        let M' := max 0 M
        use M'
        intro x ⟨ω, hω, hx⟩; subst hx
        calc |T.toFun ω|
          _ ≤ M * comass ω := hM ω
          _ ≤ M' * comass ω := mul_le_mul_of_nonneg_right (le_max_right 0 M) (comass_nonneg ω)
          _ ≤ M' * 1 := mul_le_mul_of_nonneg_left hω (le_max_left 0 M)
          _ = M' := mul_one M'
      · use ψ', hcom.le, rfl
    have : T.toFun ψ = r * T.toFun ψ' := by
      have : ψ = r • ψ' := by
        unfold ψ' r
        rw [smul_smul, mul_inv_cancel (ne_of_gt hr), one_smul]
      rw [this, T.map_smul]
    rw [this, abs_mul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left this (le_of_lt hr)

/-- **Federer-Fleming Evaluation Estimate** (Federer-Fleming, 1960).
    The evaluation of a current on a smooth form is bounded by the flat norm of the
    current and the maximum comass of the form and its derivative.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960]. -/
theorem eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ flatNorm T * max (comass ψ) (comass (smoothExtDeriv ψ)) := by
  let C := max (comass ψ) (comass (smoothExtDeriv ψ))
  have hC : 0 ≤ C := le_trans (comass_nonneg ψ) (le_max_left _ _)
  apply le_mul_of_ge_sInf hC
  · use Current.mass T
    refine ⟨T, 0, ?_, rfl⟩
    ext ω; simp [Current.boundary, Current.add_curr, Current.zero, Current.mass_zero]
  · intro r hr
    obtain ⟨S, V, hT, hr_eq⟩ := hr
    rw [← hr_eq]
    calc |T.toFun ψ|
      _ = |(S + Current.boundary V).toFun ψ| := by rw [hT]
      _ = |S.toFun ψ + (Current.boundary V).toFun ψ| := rfl
      _ = |S.toFun ψ + V.toFun (smoothExtDeriv ψ)| := by simp [Current.boundary]
      _ ≤ |S.toFun ψ| + |V.toFun (smoothExtDeriv ψ)| := abs_add _ _
      _ ≤ Current.mass S * comass ψ + Current.mass V * comass (smoothExtDeriv ψ) :=
        add_le_add (eval_le_mass S ψ) (eval_le_mass V (smoothExtDeriv ψ))
      _ ≤ Current.mass S * C + Current.mass V * C := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Current.mass_nonneg S)
        · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Current.mass_nonneg V)
      _ = (Current.mass S + Current.mass V) * C := by ring

/-- The flat norm is bounded above by the mass. -/
theorem flatNorm_le_mass {k : ℕ} (T : Current n X k) : flatNorm T ≤ Current.mass T := by
  apply sInf_le
  use T, 0
  constructor
  · ext ω; simp [Current.boundary, Current.add_curr, Current.zero]
  · simp [Current.mass_zero]

/-- The flat norm satisfies the triangle inequality. -/
theorem flatNorm_add_le {k : ℕ} (S T : Current n X k) : flatNorm (S + T) ≤ flatNorm S + flatNorm T := by
  apply Real.sInf_add_le_sInf_add
  · use Current.mass S + Current.mass (0 : Current n X (k + 1)), S, 0
    ext ω; simp [Current.boundary, Current.add_curr, Current.zero, Current.mass_zero]
  · use Current.mass T + Current.mass (0 : Current n X (k + 1)), T, 0
    ext ω; simp [Current.boundary, Current.add_curr, Current.zero, Current.mass_zero]
  · intro r1 hr1 r2 hr2
    obtain ⟨S1, V1, hS, hr1_eq⟩ := hr1
    obtain ⟨S2, V2, hT, hr2_eq⟩ := hr2
    apply sInf_le
    use S1 + S2, V1 + V2
    constructor
    · rw [hS, hT]; ext ω; simp [Current.add_curr, Current.boundary]; ring
    · rw [← hr1_eq, ← hr2_eq]
      calc Current.mass (S1 + S2) + Current.mass (V1 + V2)
        _ ≤ (Current.mass S1 + Current.mass S2) + (Current.mass V1 + Current.mass V2) := add_le_add (Current.mass_add_le _ _) (Current.mass_add_le _ _)
        _ = (Current.mass S1 + Current.mass V1) + (Current.mass S2 + Current.mass V2) := by ring

theorem flatNorm_neg {k : ℕ} (T : Current n X k) : flatNorm (-T) = flatNorm T := by
  unfold flatNorm
  have : { r | ∃ S V, -T = S + Current.boundary V ∧ Current.mass S + Current.mass V = r } = 
         { r | ∃ S V, T = S + Current.boundary V ∧ Current.mass S + Current.mass V = r } := by
    ext r; constructor
    · intro ⟨S, V, h, hr⟩
      use -S, -V
      constructor
      · rw [h]; ext ω; simp [Current.add_curr, Current.neg_curr, Current.boundary]
      · rw [Current.mass_neg, Current.mass_neg, hr]
    · intro ⟨S, V, h, hr⟩
      use -S, -V
      constructor
      · rw [h]; ext ω; simp [Current.add_curr, Current.neg_curr, Current.boundary]
      · rw [Current.mass_neg, Current.mass_neg, hr]
  rw [this]

theorem flatNorm_eq_zero_iff {k : ℕ} (T : Current n X k) : flatNorm T = 0 ↔ T = 0 := by
  constructor
  · intro h
    ext ψ
    have := eval_le_flatNorm T ψ
    rw [h, zero_mul] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  · intro h; subst h; exact flatNorm_zero

theorem flatNorm_smul {k : ℕ} (c : ℝ) (T : Current n X k) : flatNorm (c • T) = |c| * flatNorm T := by
  if hc : c = 0 then
    subst hc; simp [flatNorm_zero]
    have h0 : (0 : ℝ) • T = 0 := by ext ω; simp [Current.smul_curr, Current.zero]
    rw [h0, flatNorm_zero]
  else
    unfold flatNorm
    have h_set : { r | ∃ S V, c • T = S + Current.boundary V ∧ Current.mass S + Current.mass V = r } = 
           (fun r => |c| * r) '' { r | ∃ S V, T = S + Current.boundary V ∧ Current.mass S + Current.mass V = r } := by
      ext r; constructor
      · intro ⟨S, V, h, hr⟩
        use Current.mass ((1/c) • S) + Current.mass ((1/c) • V)
        constructor
        · use (1/c) • S, (1/c) • V
          constructor
          · rw [← h]
            ext ω; simp [Current.smul_curr, Current.boundary, Current.add_curr]; field_simp [hc]; ring
          · rfl
        · rw [Current.mass_smul, Current.mass_smul, ← mul_add, ← hr]; field_simp [hc, abs_nonneg c]
      · intro ⟨r', ⟨S, V, h, hr'⟩, hr⟩
        subst hr; subst hr'
        use c • S, c • V
        constructor
        · rw [h, Current.add_curr, Current.smul_curr, Current.smul_curr, Current.boundary]; ext ω; simp [Current.boundary, Current.smul_curr]; ring
        · rw [Current.mass_smul, Current.mass_smul, ← mul_add]
    rw [h_set]
    apply Real.sInf_mul_of_nonneg (abs_nonneg c)

theorem flatNorm_boundary_le {k : ℕ} (T : Current n X (k + 1)) :
    flatNorm (Current.boundary T) ≤ flatNorm T := by
  apply sInf_le_sInf
  intro r hr
  obtain ⟨S, V, hT, hr_eq⟩ := hr
  use 0, S
  constructor
  · rw [hT, Current.boundary, Current.zero, Current.add_curr, Current.boundary, Current.boundary]; ext ω; simp [Current.boundary]
  · rw [Current.mass_zero, zero_add, ← hr_eq]
    apply le_add_of_nonneg_right (Current.mass_nonneg V)

end
