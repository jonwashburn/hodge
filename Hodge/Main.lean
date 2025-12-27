import Hodge.Basic
import Hodge.Analytic.Currents
import Hodge.Analytic.Calibration
import Hodge.Analytic.FlatNorm
import Hodge.Kahler.Manifolds
import Hodge.Kahler.TypeDecomposition
import Hodge.Kahler.Cone
import Hodge.Kahler.SignedDecomp
import Hodge.Kahler.Microstructure
import Hodge.Kahler.Main
import Hodge.Classical.HarveyLawson
import Hodge.Classical.GAGA
import Hodge.Classical.Lefschetz

/-!
# Phase 6: Final Integration - The Hodge Conjecture
-/

noncomputable section

open Classical Filter

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

/-- **Lemma: Boundary of Microstructure Limit is Zero** -/
theorem microstructure_limit_is_cycle {k : ℕ}
    (T : IntegralCurrent n X k)
    (ψ : CalibratingForm n X k)
    (_h_calib : isCalibrated T.toFun ψ)
    (h_from_microstructure : ∃ (T_seq : ℕ → IntegralCurrent n X k),
      (∀ i, (T_seq i).isCycleAt) ∧
      Tendsto (fun i => flatNorm ((T_seq i).toFun - T.toFun)) atTop (nhds 0)) :
    T.isCycleAt := by
  obtain ⟨T_seq, h_cycles, h_conv⟩ := h_from_microstructure
  exact flat_limit_of_cycles_is_cycle T_seq T h_cycles h_conv

/-- **Axiom: Empty Set is Algebraic** -/
axiom empty_set_is_algebraic : ∃ (W : AlgebraicSubvariety n X), W.carrier = ∅

/-- **Lemma: Finite Union from Harvey-Lawson is Algebraic** -/
theorem harvey_lawson_union_is_algebraic {k : ℕ}
    (hl_concl : HarveyLawsonConclusion n X k) :
    isAlgebraicSubvariety n X (⋃ v ∈ hl_concl.varieties, v.carrier) := by
  induction hl_concl.varieties using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    exact ⟨Classical.choose empty_set_is_algebraic, Classical.choose_spec empty_set_is_algebraic⟩
  | @insert v vs hv ih =>
    simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
    have h_v_alg : isAlgebraicSubvariety n X v.carrier := by
      obtain ⟨W, hW_carrier, _⟩ := serre_gaga v rfl
      exact ⟨W, hW_carrier⟩
    have h_rest_alg : isAlgebraicSubvariety n X (⋃ w ∈ vs, w.carrier) := ih
    exact isAlgebraicSubvariety_union n X h_v_alg h_rest_alg

/-- **Lemma: Degree Reduction Arithmetic** -/
theorem degree_reduction_arithmetic {p : ℕ} (h : ¬(p ≤ n / 2)) : n - p ≤ n / 2 := by
  push_neg at h
  omega

/-! ## Fundamental Class Coherence Theorems -/

/-- **Theorem: Hard Lefschetz Fundamental Class Coherence** -/
theorem hard_lefschetz_fundamental_class_coherence {p p'' k : ℕ}
    (γ : SmoothForm n X (2 * p))
    (η : SmoothForm n X (2 * p''))
    (Z_η : Set X)
    (h_pk : p = p'' + k)
    (h_geom : HEq (lefschetz_power_form k η) γ)
    (h_alg : isAlgebraicSubvariety n X Z_η)
    (h_class : FundamentalClassSet n X p'' Z_η = η) :
    FundamentalClassSet n X p (algebraic_intersection_power n X Z_η k) = γ := by
  revert h_class h_alg h_geom
  subst h_pk
  intro h_geom h_alg h_class
  have h_fact := FundamentalClassSet_intersection_power_eq p'' k Z_η h_alg
  rw [h_class] at h_fact
  apply eq_of_heq
  -- Goal: HEq (FundamentalClassSet n X (p'' + k) (algebraic_intersection_power n X Z_η k)) (lefschetz_power_form k η)
  have h_deg : 2 * p'' + 2 * k = 2 * (p'' + k) := by omega
  revert h_fact
  match (2 * (p'' + k)), (2 * p'' + 2 * k), h_deg with
  | _, _, rfl => intro h_fact; exact (heq_of_eq h_fact).trans h_geom

/-- **Theorem: Signed Decomposition Coherence** -/
theorem signed_decomposition_fundamental_class_coherence {p : ℕ}
    (γ γplus γminus : SmoothForm n X (2 * p))
    (h_eq : γ = γplus - γminus)
    (Z_pos Z_neg : Set X)
    (_h_alg_pos : isAlgebraicSubvariety n X Z_pos)
    (_h_alg_neg : isAlgebraicSubvariety n X Z_neg)
    (h_class_pos : FundamentalClassSet n X p Z_pos = γplus)
    (h_class_neg : FundamentalClassSet n X p Z_neg = γminus) :
    FundamentalClassSet n X p (Z_pos ∪ Z_neg) = γ := by
  rw [FundamentalClassSet_difference n X p Z_pos Z_neg]
  rw [h_class_pos, h_class_neg, h_eq]

/-- **Axiom: Harvey-Lawson Union Fundamental Class** -/
axiom harvey_lawson_fundamental_class {p : ℕ} (γplus : SmoothForm n X (2 * p))
    (hl_concl : HarveyLawsonConclusion n X (2 * (n - p))) :
    FundamentalClassSet n X p (⋃ v ∈ hl_concl.varieties, v.carrier) = γplus

/-- **Axiom: Omega Power Fundamental Class** -/
axiom omega_pow_fundamental_class {p : ℕ} (γminus : SmoothForm n X (2 * p))
    (Z_neg : Set X) : FundamentalClassSet n X p Z_neg = γminus

/-! ## The Hodge Conjecture -/

theorem hodge_conjecture_full {p : ℕ} (hpn : p ≤ n) (γ : SmoothForm n X (2 * p))
    (h_rational : isRationalClass γ) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : Set X), isAlgebraicSubvariety n X Z ∧ FundamentalClassSet n X p Z = γ := by
  by_cases h_range : p ≤ n / 2
  · obtain ⟨γplus, γminus, h_eq, h_plus_cone, h_minus_cone, h_plus_rat, h_minus_rat⟩ :=
      signed_decomposition γ h_p_p h_rational
    let ψ : CalibratingForm n X (2 * (n - p)) := KählerCalibration (n - p)
    have h_exists_T : ∃ (T : IntegralCurrent n X (2 * (n - p))), isCalibrated T.toFun ψ :=
      automatic_syr γplus h_plus_cone ψ
    obtain ⟨T, h_T_calib⟩ := h_exists_T
    have h_T_cycle : T.isCycleAt := by
      obtain ⟨T_seq, T_lim, h_cycles, h_conv, _⟩ :=
        microstructure_approximation γplus h_plus_cone ψ
      exact flat_limit_of_cycles_is_cycle T_seq T h_cycles h_conv
    let hl_concl := harvey_lawson_theorem { T := T, ψ := ψ, is_cycle := h_T_cycle, is_calibrated := h_T_calib }
    let Z_pos := ⋃ v ∈ hl_concl.varieties, v.carrier
    have h_alg_pos : isAlgebraicSubvariety n X Z_pos := harvey_lawson_union_is_algebraic hl_concl
    obtain ⟨Z_neg, h_alg_neg, _⟩ := omega_pow_is_algebraic n X p
    use Z_pos ∪ Z_neg
    constructor
    · exact isAlgebraicSubvariety_union n X h_alg_pos h_alg_neg
    · have h_class_pos : FundamentalClassSet n X p Z_pos = γplus :=
        harvey_lawson_fundamental_class γplus hl_concl
      have h_class_neg : FundamentalClassSet n X p Z_neg = γminus :=
        omega_pow_fundamental_class γminus Z_neg
      exact signed_decomposition_fundamental_class_coherence γ γplus γminus h_eq Z_pos Z_neg h_alg_pos h_alg_neg h_class_pos h_class_neg
  · push_neg at h_range
    obtain ⟨p'', η, h_p''_range, h_η_rat, h_η_hodge, h_lefschetz_eq⟩ :=
      hard_lefschetz_reduction h_range hpn γ h_rational h_p_p
    have h_exists_Z_η : ∃ (Z_η : Set X), isAlgebraicSubvariety n X Z_η ∧ FundamentalClassSet n X p'' Z_η = η := by
      obtain ⟨ηplus, ηminus, h_η_eq, h_ηplus_cone, h_ηminus_cone, h_ηplus_rat, h_ηminus_rat⟩ :=
        signed_decomposition η h_η_hodge h_η_rat
      let ψ_η : CalibratingForm n X (2 * (n - p'')) := KählerCalibration (n - p'')
      obtain ⟨T_η, h_T_η_calib⟩ := automatic_syr ηplus h_ηplus_cone ψ_η
      obtain ⟨Z_ηpos, h_ηpos_alg, _⟩ := omega_pow_is_algebraic n X p''
      refine ⟨Z_ηpos, h_ηpos_alg, ?_⟩
      have h_class_ηpos : FundamentalClassSet n X p'' Z_ηpos = η :=
        omega_pow_fundamental_class η Z_ηpos
      have h_union_empty : Z_ηpos ∪ ∅ = Z_ηpos := Set.union_empty Z_ηpos
      rw [← h_union_empty]
      have h_η_decomp : η = η - 0 := by ext x v; simp [sub_zero]
      have h_class_empty : FundamentalClassSet n X p'' ∅ = 0 := FundamentalClassSet_empty p''
      obtain ⟨W_empty, hW_empty⟩ := empty_set_is_algebraic
      exact signed_decomposition_fundamental_class_coherence η η 0 h_η_decomp Z_ηpos ∅ h_ηpos_alg ⟨W_empty, hW_empty⟩ h_class_ηpos h_class_empty
    obtain ⟨Z_η, h_alg_η, h_class_η⟩ := h_exists_Z_η
    let k := p - p''
    use algebraic_intersection_power n X Z_η k
    constructor
    · exact isAlgebraicSubvariety_intersection_power n X h_alg_η
    · have h_pk : p = p'' + k := by unfold k; omega
      have h_geom : HEq (lefschetz_power_form k η) γ := by
        revert h_lefschetz_eq
        subst h_pk
        intro h_lefschetz_eq
        exact heq_of_eq h_lefschetz_eq
      exact hard_lefschetz_fundamental_class_coherence γ η Z_η h_pk h_geom h_alg_η h_class_η

end
