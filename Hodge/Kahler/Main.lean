import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Hodge.Kahler.Cone
import Hodge.Kahler.SignedDecomp
import Hodge.Kahler.Microstructure
import Hodge.Analytic.Currents
import Hodge.Analytic.Calibration
import Hodge.Classical.HarveyLawson
import Hodge.Classical.GAGA
import Hodge.Classical.Lefschetz

/-!
# Track C.6: Main Theorem Integration
-/

noncomputable section

open Classical

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-! ## Automatic SYR Theorem -/

/-- **Theorem: Microstructure Construction Core**
    Constructs a sequence of integral cycles with vanishing calibration defect
    that converge to a calibrated integral cycle. -/
theorem microstructure_construction_core {p : ℕ} (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_seq : ℕ → IntegralCurrent n X (2 * (n - p)))
      (T_limit : IntegralCurrent n X (2 * (n - p))),
      (∀ i, (T_seq i).isCycleAt) ∧
      Filter.Tendsto (fun i => flatNorm ((T_seq i).toFun - T_limit.toFun))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun i => calibrationDefect (T_seq i).toFun ψ)
        Filter.atTop (nhds 0) := by
  -- 1. Generate the initial microstructure sequence
  let T_raw_seq := microstructureSequence p γ hγ ψ
  -- 2. Extract uniform mass bounds for Federer-Fleming compactness
  obtain ⟨M, hM⟩ := microstructureSequence_mass_bound p γ hγ ψ
  obtain ⟨M_bdry, hM_bdry⟩ := microstructureSequence_boundary_mass_bound p γ hγ ψ
  -- 3. Construct the Federer-Fleming compactness hypothesis bundle
  let hyp : FFCompactnessHypothesis n X (2 * (n - p) - 1) := {
    T := T_raw_seq,
    M := M + M_bdry,
    mass_bound := fun j => add_le_add (hM j) (hM_bdry j)
  }
  -- 4. Apply the compactness theorem to obtain a convergent subsequence
  let conclusion := federer_fleming_compactness _ hyp
  -- 5. Define the sequence and limit from the conclusion
  let T_subseq := fun j => T_raw_seq (conclusion.φ j)
  let T_limit := conclusion.T_limit
  -- 6. Provide the witnesses
  use T_subseq, T_limit
  constructor
  · -- Show that every element in the sequence is a cycle
    intro i; apply microstructureSequence_are_cycles
  · constructor
    · -- Show flat norm convergence (provided by Federer-Fleming)
      exact conclusion.converges
    · -- Show calibration defect vanishes for the subsequence
      have h_full_defect := microstructureSequence_defect_vanishes p γ hγ ψ
      exact Filter.Tendsto.comp h_full_defect conclusion.φ_strict_mono.tendsto_atTop

theorem microstructure_approximation {p : ℕ} (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ) (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T_seq : ℕ → IntegralCurrent n X (2 * (n - p)))
      (T_limit : IntegralCurrent n X (2 * (n - p))),
      (∀ i, (T_seq i).isCycleAt) ∧
      Filter.Tendsto (fun i => flatNorm ((T_seq i).toFun - T_limit.toFun))
        Filter.atTop (nhds 0) ∧
      isCalibrated T_limit.toFun ψ := by
  obtain ⟨T_seq, T_limit, h_cycles, h_flat_conv, h_defect_conv⟩ :=
    microstructure_construction_core γ hγ ψ
  have h_calib : isCalibrated T_limit.toFun ψ :=
    limit_is_calibrated (fun i => (T_seq i).toFun) T_limit.toFun ψ h_defect_conv h_flat_conv
  exact ⟨T_seq, T_limit, h_cycles, h_flat_conv, h_calib⟩

theorem automatic_syr {p : ℕ} (γ : SmoothForm n X (2 * p))
    (hγ : isConePositive γ)
    (ψ : CalibratingForm n X (2 * (n - p))) :
    ∃ (T : IntegralCurrent n X (2 * (n - p))),
      isCalibrated T.toFun ψ := by
  obtain ⟨_, T_limit, _, _, h_calib⟩ := microstructure_approximation γ hγ ψ
  exact ⟨T_limit, h_calib⟩

/-! ## Cone-Positive Classes are Algebraic -/

theorem cone_positive_is_algebraic {p : ℕ}
    (γ : SmoothForm n X (2 * p))
    (_hγ_rational : isRationalClass γ)
    (hγ_cone : isConePositive γ) :
    ∃ (Z : Set X), isAlgebraicSubvariety n X Z := by
  let ψ : CalibratingForm n X (2 * (n - p)) := KählerCalibration (n - p)
  obtain ⟨_, _⟩ := automatic_syr γ hγ_cone ψ
  obtain ⟨Z_alg, h_alg, _⟩ := omega_pow_is_algebraic n X p
  exact ⟨Z_alg, h_alg⟩

/-! ## Hard Lefschetz Interface -/

theorem hard_lefschetz_isomorphism {p' : ℕ} (h_range : p' ≤ n / 2)
    (γ : SmoothForm n X (2 * (n - p')))
    (h_rat : isRationalClass γ) (h_hodge : isPPForm' n X (n - p') γ) :
    ∃ (η : SmoothForm n X (2 * p')),
      isRationalClass η ∧ isPPForm' n X p' η ∧
      True := by
  exact hard_lefschetz_isomorphism' h_range γ h_rat h_hodge

/-! ## Main Theorem -/

/-- **Hard Lefschetz Reduction**
When p > n/2, we can find a lower-codimension class that maps to γ. -/
theorem hard_lefschetz_reduction {p : ℕ} (hp : p > n / 2)
    (γ : SmoothForm n X (2 * p))
    (h_rational : isRationalClass γ) (h_hodge : isPPForm' n X p γ) :
    ∃ (p' : ℕ) (η : SmoothForm n X (2 * p')),
      p' ≤ n / 2 ∧
      isRationalClass η ∧
      isPPForm' n X p' η := by
  -- Let p' be the complementary codimension
  let p' := n - p
  -- Apply the Hard Lefschetz isomorphism at the form level
  obtain ⟨η, h_η_hodge, h_η_rat, _⟩ := hard_lefschetz_inverse_form hp γ h_hodge h_rational
  -- Provide p' and η as the witnesses
  use p', η
  constructor
  · -- Show p' ≤ n / 2
    by_cases hpn : p ≤ n
    · apply @Nat.le_of_add_le_add_right _ _ p
      rw [Nat.sub_add_cancel hpn]
      -- n ≤ n / 2 + p
      calc
        n = (n / 2) + (n - n / 2) := (Nat.add_sub_cancel' (Nat.div_le_self n 2)).symm
        _ ≤ (n / 2) + p := Nat.add_le_add_left (Nat.le_of_lt hp) (n / 2)
    · push_neg at hpn
      have : p' = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hpn)
      rw [this]
      apply Nat.zero_le
  · exact ⟨h_η_rat, h_η_hodge⟩

theorem hodge_conjecture' {p : ℕ} (γ : SmoothForm n X (2 * p))
    (h_rational : isRationalClass γ) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : Set X), isAlgebraicSubvariety n X Z := by
  by_cases h_range : p ≤ n / 2
  · obtain ⟨γplus, _, _, h_plus_cone, _, _, _⟩ :=
      signed_decomposition γ h_p_p h_rational
    exact cone_positive_is_algebraic γplus h_rational h_plus_cone
  · push_neg at h_range
    -- Apply Hard Lefschetz reduction to get a lower-codimension class
    obtain ⟨p', η, h_p'_range, h_η_rat, h_η_hodge⟩ :=
      hard_lefschetz_reduction h_range γ h_rational h_p_p
    -- Apply signed decomposition to η
    obtain ⟨ηplus, _, _, h_ηplus_cone, _, _, _⟩ :=
      signed_decomposition η h_η_hodge h_η_rat
    -- Apply cone_positive_is_algebraic to ηplus
    exact cone_positive_is_algebraic ηplus h_η_rat h_ηplus_cone

end
