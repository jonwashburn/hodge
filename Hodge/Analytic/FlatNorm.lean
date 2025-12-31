import Hodge.Analytic.Currents
import Hodge.Analytic.Norms
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!

This file defines the flat norm on currents and proves its basic properties.
The flat norm is the natural metric for the space of integral currents.

Since `Current` operations are opaque, most properties are axiomatized.
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
  sInf { r | ∃ S R, T = S + Current.boundary R ∧ r = Current.mass S + Current.mass R }

/-- The flat norm is non-negative. -/
theorem flatNorm_nonneg {k : ℕ} (T : Current n X k) : flatNorm T ≥ 0 := by
  apply Real.sInf_nonneg
  intro r ⟨S, R, _, hr⟩
  rw [hr]
  apply add_nonneg (Current.mass_nonneg S) (Current.mass_nonneg R)

/-- The flat norm of the zero current is zero. -/
theorem flatNorm_zero {k : ℕ} : flatNorm (0 : Current n X k) = 0 := by
  unfold flatNorm
  have h : (0 : ℝ) ∈ { r | ∃ S R, (0 : Current n X k) = S + Current.boundary R ∧ r = Current.mass S + Current.mass R } := by
    use 0, 0
    simp [Current.mass_zero]
  -- We need to show that 0 is the infimum. Since all elements are ≥ 0 and 0 is in the set, sInf is 0.
  apply le_antisymm
  · apply csInf_le
    · use 0
      intro r ⟨S, R, hSR, hr⟩
      rw [hr]
      apply add_nonneg (Current.mass_nonneg S) (Current.mass_nonneg R)
    · exact h
  · apply Real.sInf_nonneg
    intro r ⟨S, R, hSR, hr⟩
    rw [hr]
    apply add_nonneg (Current.mass_nonneg S) (Current.mass_nonneg R)

/-- Bound evaluation by mass. -/
theorem eval_le_mass {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ Current.mass T * comass ψ := by
  by_cases h : comass ψ > 0
  · have h1 : |T.toFun ψ| / comass ψ ∈ { r | ∃ ψ', comass ψ' > 0 ∧ r = |T.toFun ψ'| / comass ψ' } := ⟨ψ, h, rfl⟩
    have h2 := le_csSup _ h1
    · rw [le_div_iff h] at h2
      exact h2
    · -- Need to show the set is bounded above.
      obtain ⟨M, hM⟩ := Current.is_bounded T
      use M
      intro r ⟨ψ', hψ', hr⟩
      rw [hr]
      apply div_le_of_le_mul hψ' (abs_nonneg _)
      exact hM ψ'
  · have h0 : comass ψ = 0 := by
      have hneg := not_lt.mp h
      have hpos := comass_nonneg ψ
      linarith
    rw [h0, mul_zero]
    -- If comass ψ = 0, then ψ = 0 (by comass_eq_zero_iff)
    -- But we don't necessarily have comass_eq_zero_iff here.
    -- However, |T.toFun ψ| ≤ M * comass ψ, so |T.toFun ψ| ≤ M * 0 = 0.
    obtain ⟨M, hM⟩ := Current.is_bounded T
    have h_bound := hM ψ
    rw [h0, mul_zero] at h_bound
    exact h_bound

/-- The flat norm is bounded above by the mass. -/
theorem flatNorm_le_mass {k : ℕ} (T : Current n X k) : flatNorm T ≤ Current.mass T := by
  unfold flatNorm
  apply csInf_le
  · use 0
    intro r ⟨S, R, hSR, hr⟩
    rw [hr]
    apply add_nonneg (Current.mass_nonneg S) (Current.mass_nonneg R)
  · use T, 0
    simp [Current.mass_zero]

/-- **Infimum Multiplication Lemma** (Standard). -/
theorem le_csInf_mul {L : ℝ} {s : Set ℝ} {c : ℝ} (hc : c > 0) (hs : s.Nonempty)
    (h_le : ∀ x ∈ s, |L| ≤ x * c) : |L| ≤ sInf s * c := by
  have : |L| / c ≤ sInf s := by
    apply le_csInf hs
    intro x hx
    rw [le_div_iff hc]
    exact h_le x hx
  rw [le_div_iff hc] at this
  exact this

/-- **Non-emptiness of the Flat Norm Set** (Standard).
    For any current T, the set of its decompositions T = S + ∂R is nonempty.
    A trivial witness is S = T and R = 0. -/
theorem exists_flatNorm_set_nonempty {k : ℕ} (T : Current n X k) :
    {r | ∃ S R, T = S + Current.boundary R ∧ r = Current.mass S + Current.mass R}.Nonempty := by
  use Current.mass T + Current.mass (0 : Current n X (k + 1))
  use T, 0
  simp [Current.mass_zero]

/-- The flat norm satisfies the triangle inequality. -/
theorem flatNorm_add_le {k : ℕ} (S T : Current n X k) : flatNorm (S + T) ≤ flatNorm S + flatNorm T := by
  unfold flatNorm
  apply Real.le_sInf_add_sInf
  · apply exists_flatNorm_set_nonempty S
  · apply exists_flatNorm_set_nonempty T
  · use 0
    rintro r ⟨S1, R1, _, rfl⟩
    apply add_nonneg (Current.mass_nonneg S1) (Current.mass_nonneg R1)
  · use 0
    rintro r ⟨S2, R2, _, rfl⟩
    apply add_nonneg (Current.mass_nonneg S2) (Current.mass_nonneg R2)
  · rintro r1 ⟨S1, R1, hS1, rfl⟩ r2 ⟨S2, R2, hS2, rfl⟩
    use S1 + S2, R1 + R2
    constructor
    · rw [hS1, hS2]
      simp [Current.boundary, Current.add_curr]
      ext ω; simp [Current.add_curr, Current.boundary]
      ring
    · calc Current.mass (S1 + S2) + Current.mass (R1 + R2)
        _ ≤ (Current.mass S1 + Current.mass S2) + (Current.mass R1 + Current.mass R2) := by
            apply add_le_add
            · exact Current.mass_add_le S1 S2
            · exact Current.mass_add_le R1 R2
        _ = (Current.mass S1 + Current.mass R1) + (Current.mass S2 + Current.mass R2) := by ring

/-- **Federer-Fleming Evaluation Estimate** (Federer-Fleming, 1960).
    The evaluation of a current on a smooth form is bounded by the flat norm of the
    current and the maximum comass of the form and its derivative.
    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents", 1960, Section 4]. -/
theorem eval_le_flatNorm {k : ℕ} (T : Current n X k) (ψ : SmoothForm n X k) :
    |T.toFun ψ| ≤ flatNorm T * max (comass ψ) (comass (smoothExtDeriv ψ)) := by
  unfold flatNorm
  let C := max (comass ψ) (comass (smoothExtDeriv ψ))
  have hC : 0 ≤ C := le_max_of_le_left (comass_nonneg ψ)
  by_cases hC_pos : C > 0
  · apply le_csInf_mul hC_pos
    · apply exists_flatNorm_set_nonempty T
    · rintro r ⟨S, R, hT, rfl⟩
      have h_eval : T.toFun ψ = S.toFun ψ + R.toFun (smoothExtDeriv ψ) := by
        rw [hT]; simp [Current.add_curr, Current.boundary]
      rw [h_eval]
      calc |S.toFun ψ + R.toFun (smoothExtDeriv ψ)|
        _ ≤ |S.toFun ψ| + |R.toFun (smoothExtDeriv ψ)| := abs_add _ _
        _ ≤ Current.mass S * comass ψ + Current.mass R * comass (smoothExtDeriv ψ) := by
            apply add_le_add
            · exact eval_le_mass S ψ
            · exact eval_le_mass R (smoothExtDeriv ψ)
        _ ≤ Current.mass S * C + Current.mass R * C := by
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left (le_max_left _ _) (Current.mass_nonneg S)
            · apply mul_le_mul_of_nonneg_left (le_max_right _ _) (Current.mass_nonneg R)
        _ = (Current.mass S + Current.mass R) * C := by ring
  · have hC_zero : C = 0 := by
      have : C ≥ 0 := hC
      linarith
    have h_comass : comass ψ = 0 := by
      have : comass ψ ≤ C := le_max_left _ _
      rw [hC_zero] at this
      linarith [comass_nonneg ψ]
    rw [hC_zero, mul_zero]
    obtain ⟨M, hM⟩ := Current.is_bounded T
    have h_bound := hM ψ
    rw [h_comass, mul_zero] at h_bound
    exact h_bound

/-- The flat norm is symmetric under negation. -/
theorem flatNorm_neg {k : ℕ} (T : Current n X k) : flatNorm (-T) = flatNorm T := by
  unfold flatNorm
  congr
  ext r
  constructor
  · intro ⟨S, R, h, hr⟩
    use -S, -R
    constructor
    · rw [h]; simp [Current.boundary]; ext ω; simp [Current.neg_curr]
    · simp [hr, Current.mass_neg]
  · intro ⟨S, R, h, hr⟩
    use -S, -R
    constructor
    · rw [h]; simp [Current.boundary]; ext ω; simp [Current.neg_curr]
    · simp [hr, Current.mass_neg]

/-- A current is zero iff its flat norm is zero. -/
theorem flatNorm_eq_zero_iff {k : ℕ} (T : Current n X k) : flatNorm T = 0 ↔ T = 0 := by
  constructor
  · intro h
    -- If flatNorm T = 0, then for any ε > 0, there exists a decomposition T = S + ∂R
    -- such that mass S + mass R < ε.
    ext ψ
    have h_zero : ∀ ε > 0, |T.toFun ψ| < ε * (comass ψ + comass (smoothExtDeriv ψ) + 1) := by
      intro ε hε
      obtain ⟨r, ⟨S, R, hT, rfl⟩, hr_lt⟩ : ∃ r ∈ { r | ∃ S R, T = S + Current.boundary R ∧ r = Current.mass S + Current.mass R }, r < ε := by
        apply exists_lt_of_sInf_lt (exists_flatNorm_set_nonempty T)
        rw [h]
        exact hε
      have h_eval : T.toFun ψ = S.toFun ψ + R.toFun (smoothExtDeriv ψ) := by
        rw [hT]; simp [Current.add_curr, Current.boundary]
      rw [h_eval]
      calc |S.toFun ψ + R.toFun (smoothExtDeriv ψ)|
        _ ≤ |S.toFun ψ| + |R.toFun (smoothExtDeriv ψ)| := abs_add _ _
        _ ≤ Current.mass S * comass ψ + Current.mass R * comass (smoothExtDeriv ψ) := by
            apply add_le_add
            · exact eval_le_mass S ψ
            · exact eval_le_mass R (smoothExtDeriv ψ)
        _ ≤ (Current.mass S + Current.mass R) * (comass ψ + comass (smoothExtDeriv ψ) + 1) := by
            have h1 : comass ψ ≤ comass ψ + comass (smoothExtDeriv ψ) + 1 := by linarith [comass_nonneg (smoothExtDeriv ψ)]
            have h2 : comass (smoothExtDeriv ψ) ≤ comass ψ + comass (smoothExtDeriv ψ) + 1 := by linarith [comass_nonneg ψ]
            calc Current.mass S * comass ψ + Current.mass R * comass (smoothExtDeriv ψ)
              _ ≤ Current.mass S * (comass ψ + comass (smoothExtDeriv ψ) + 1) + Current.mass R * (comass ψ + comass (smoothExtDeriv ψ) + 1) := by
                  apply add_le_add
                  · exact mul_le_mul_of_nonneg_left h1 (Current.mass_nonneg S)
                  · exact mul_le_mul_of_nonneg_left h2 (Current.mass_nonneg R)
              _ = (Current.mass S + Current.mass R) * (comass ψ + comass (smoothExtDeriv ψ) + 1) := by ring
        _ < ε * (comass ψ + comass (smoothExtDeriv ψ) + 1) := by
            apply mul_lt_mul_of_pos_right hr_lt
            linarith [comass_nonneg ψ, comass_nonneg (smoothExtDeriv ψ)]
    have h_abs_zero : |T.toFun ψ| = 0 := by
      apply Real.eq_zero_of_nonneg_of_forall_lt_pos (abs_nonneg _)
      intro ε hε
      let C := comass ψ + comass (smoothExtDeriv ψ) + 1
      have hC : C > 0 := by linarith [comass_nonneg ψ, comass_nonneg (smoothExtDeriv ψ)]
      let ε' := ε / C
      have hε' : ε' > 0 := div_pos hε hC
      have h_bound := h_zero ε' hε'
      rw [div_mul_cancel₀ ε (ne_of_gt hC)] at h_bound
      exact h_bound
    exact abs_eq_zero.mp h_abs_zero
  · intro h; rw [h, flatNorm_zero]

/-- Flat norm scales with absolute value of scalar. -/
theorem flatNorm_smul {k : ℕ} (c : ℝ) (T : Current n X k) : flatNorm (c • T) = |c| * flatNorm T := by
  unfold flatNorm
  by_cases hc : c = 0
  · subst hc; simp [flatNorm_zero, Current.mass_zero]; rw [abs_zero, zero_mul]
  · rw [Real.mul_sInf_of_nonneg (abs_nonneg c)]
    · congr
      ext r
      constructor
      · rintro ⟨S, R, h, rfl⟩
        use (1/c) • S, (1/c) • R
        constructor
        · have h_inv : T = (1/c) • (c • T) := by field_simp; ring_nf
          rw [h_inv, h]
          simp [Current.boundary, Current.smul_curr, Current.add_curr]
          ext ω; simp [Current.smul_curr, Current.boundary, Current.add_curr]
          ring
        · rw [Current.mass_smul, Current.mass_smul]
          field_simp [abs_mul]
          ring
      · rintro ⟨r', ⟨S, R, h, rfl⟩, rfl⟩
        use c • S, c • R
        constructor
        · rw [h]; simp [Current.boundary, Current.smul_curr, Current.add_curr]
          ext ω; simp [Current.smul_curr, Current.boundary, Current.add_curr]
          ring
        · rw [Current.mass_smul, Current.mass_smul]
          ring
    · apply exists_flatNorm_set_nonempty T

/-- The flat norm of a boundary is at most the flat norm of the original current. -/
theorem flatNorm_boundary_le {k : ℕ} (T : Current n X (k + 1)) :
    flatNorm (Current.boundary T) ≤ flatNorm T := by
  unfold flatNorm
  apply Real.le_sInf_sInf
  · apply exists_flatNorm_set_nonempty (Current.boundary T)
  · rintro r ⟨S, R, hT, rfl⟩
    have h_bdy_T : Current.boundary T = 0 + Current.boundary S := by
      rw [hT]; simp [Current.boundary_boundary, Current.add_curr]; ext ω; simp [Current.boundary, Current.add_curr]
    have h_in_set : mass (0 : Current n X k) + mass S ∈ { r' | ∃ S' R', Current.boundary T = S' + Current.boundary R' ∧ r' = Current.mass S' + Current.mass R' } := by
      use 0, S, h_bdy_T, rfl
    calc sInf { r' | ∃ S' R', Current.boundary T = S' + Current.boundary R' ∧ r' = Current.mass S' + Current.mass R' }
      _ ≤ mass (0 : Current n X k) + mass S := csInf_le (exists_flatNorm_set_bddBelow _) h_in_set
      _ = mass S := by rw [Current.mass_zero, zero_add]
      _ ≤ mass S + mass R := by
          have : mass R ≥ 0 := Current.mass_nonneg R
          linarith

/-- **Boundedness Below of the Flat Norm Set** (Standard).
    The masses of all decomposition components are non-negative, so the set
    is bounded below by zero. -/
theorem exists_flatNorm_set_bddBelow {k : ℕ} (T : Current n X k) :
    BddBelow {r | ∃ S R, T = S + Current.boundary R ∧ r = Current.mass S + Current.mass R} := by
  use 0
  rintro r ⟨S, R, _, rfl⟩
  apply add_nonneg (Current.mass_nonneg S) (Current.mass_nonneg R)

end
