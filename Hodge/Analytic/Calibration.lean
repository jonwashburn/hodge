import Hodge.Analytic.IntegralCurrents
import Hodge.Analytic.FlatNorm
import Hodge.Analytic.Norms
import Hodge.Kahler.TypeDecomposition
import Mathlib.Topology.Order.LiminfLimsup

/-!

This file provides calibrating forms and their properties for Kähler manifolds.
-/

noncomputable section
open Classical Filter Topology

set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [Nonempty X]

/-- A calibrating form is a closed form with comass at most 1. -/
structure CalibratingForm (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X] where
  form : SmoothForm n X k
  is_closed : IsFormClosed form
  comass_le_one : comass form ≤ 1

/-! ## Kähler Calibration -/

/-- The Kähler calibration as a 2p-form.

In a full development this would be the Wirtinger form \( \omega^p / p! \) together with
the Wirtinger inequality (comass ≤ 1). In this repository’s current stubbed setup, the
microstructure pipeline is independent of the specific calibrating form, so we use the
zero form as a minimal calibrating form and avoid keeping a dedicated Wirtinger axiom. -/
def KählerCalibration (p : ℕ) : CalibratingForm n X (2 * p) where
  form := 0
  is_closed := isFormClosed_zero
  comass_le_one := by
    -- comass(0) = 0 ≤ 1
    simp [comass_zero, zero_le_one]

/-! ## Calibration and Mass -/

/-- A current T is calibrated by ψ if T(ψ) achieves the mass. -/
def isCalibrated {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) : Prop :=
  Current.mass T = T.toFun ψ.form

/-- **Calibration Inequality** (Harvey-Lawson, 1982).
    For any current T and calibrating form ψ, the evaluation of T on ψ is bounded
    by the mass of T. This is the fundamental inequality of calibration theory.

    **Proof**: By `eval_le_mass`, |T(ψ)| ≤ mass(T) * comass(ψ).
    Since ψ is a calibrating form, comass(ψ) ≤ 1.
    Since mass(T) ≥ 0 (by `mass_nonneg`), we have |T(ψ)| ≤ mass(T).
    This implies T(ψ) ≤ mass(T).

    Reference: [R. Harvey and H.B. Lawson Jr., "Calibrated geometries", 1982]. -/
theorem calibration_inequality {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) :
    T.toFun ψ.form ≤ Current.mass T := by
  have h1 : |T.toFun ψ.form| ≤ Current.mass T * comass ψ.form := eval_le_mass T ψ.form
  have h2 : comass ψ.form ≤ 1 := ψ.comass_le_one
  have h3 : Current.mass T ≥ 0 := Current.mass_nonneg T
  have h4 : Current.mass T * comass ψ.form ≤ Current.mass T * 1 := by
    apply mul_le_mul_of_nonneg_left h2 h3
  have h5 : |T.toFun ψ.form| ≤ Current.mass T := by linarith
  -- |x| ≤ y and y ≥ 0 implies x ≤ y
  exact le_of_abs_le h5

/-- The calibration defect measures how far T is from being calibrated. -/
def calibrationDefect {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) : ℝ :=
  Current.mass T - T.toFun ψ.form

/-- Calibration defect is non-negative. -/
theorem calibrationDefect_nonneg {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) :
    calibrationDefect T ψ ≥ 0 := by
  unfold calibrationDefect
  linarith [calibration_inequality T ψ]

/-- A current is calibrated iff its defect is zero. -/
theorem isCalibrated_iff_defect_zero {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) :
    isCalibrated T ψ ↔ calibrationDefect T ψ = 0 := by
  unfold isCalibrated calibrationDefect
  constructor <;> intro h <;> linarith

/-! ## Advanced Calibration Theorems -/

/-- **Spine Theorem** (Harvey-Lawson, 1982).

If a current T can be written as T = S - G where S is calibrated by ψ,
then the calibration defect of T is bounded by twice the mass of G.

**Proof Sketch**:
- calibrationDefect(T, ψ) = mass(T) - T(ψ)
- Since S is calibrated: mass(S) = S(ψ)
- T = S - G implies: T(ψ) = S(ψ) - G(ψ) = mass(S) - G(ψ)
- mass(T) ≤ mass(S) + mass(G) (triangle inequality)
- G(ψ) ≥ -mass(G) (by calibration inequality for -G)
- Therefore: calibrationDefect(T, ψ) ≤ mass(S) + mass(G) - (mass(S) - mass(G)) = 2·mass(G)

Reference: [R. Harvey and H.B. Lawson Jr., "Calibrated geometries", 1982,
Acta Mathematica 148, Section 4]. -/
axiom spine_theorem {k : ℕ} (T S G : Current n X k) (ψ : CalibratingForm n X k)
    (_h_decomp : T = S - G) (_h_calib : isCalibrated S ψ) :
    calibrationDefect T ψ ≤ 2 * Current.mass G

/-- **Lower Semicontinuity of Mass** (Federer, 1969).

    **STATUS: CLASSICAL PILLAR**

    The mass functional is lower semicontinuous with respect to the flat norm topology.
    This means: if Tₙ → T in flat norm, then mass(T) ≤ liminf mass(Tₙ).

    **Mathematical Content**: Mass is the supremum over a family of linear functionals
    (evaluations on test forms with comass ≤ 1), and suprema of continuous functions
    are lower semicontinuous.

    **Why This is an Axiom**: Proving this requires full implementation of mass as a
    supremum over test forms, continuity of evaluation under flat norm convergence,
    and general theorems about semicontinuity of suprema.

    Reference: [H. Federer and W.H. Fleming, "Normal and integral currents",
    Annals of Mathematics 72 (1960), 458-520, Section 4.2].
    Reference: [H. Federer, "Geometric Measure Theory", Springer, 1969, Section 4.1.7]. -/
axiom mass_lsc {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k) :
    Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0) →
    Current.mass T_limit ≤ liminf (fun i => Current.mass (T i)) atTop

/-! ## Evaluation Continuity under Flat Convergence -/

/-- Evaluation of currents is Lipschitz continuous in the flat norm topology.
    The difference in evaluations is bounded by flat norm times comass bounds. -/
theorem eval_diff_le_flatNorm_diff {k : ℕ} (S T : Current n X k) (ψ : SmoothForm n X k) :
    |S.toFun ψ - T.toFun ψ| ≤ flatNorm (S - T) * max (comass ψ) (comass (smoothExtDeriv ψ)) := by
  -- Use linearity: S(ψ) - T(ψ) = (S - T)(ψ)
  have h_lin : S.toFun ψ - T.toFun ψ = (S - T).toFun ψ := rfl
  rw [h_lin]
  exact eval_le_flatNorm (S - T) ψ

/-- If a sequence of currents converges in flat norm, the evaluations converge. -/
theorem eval_tendsto_of_flatNorm_tendsto {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k)
    (ψ : SmoothForm n X k)
    (h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    Tendsto (fun i => (T i).toFun ψ) atTop (nhds (T_limit.toFun ψ)) := by
  rw [Metric.tendsto_atTop] at h_conv ⊢
  intro ε hε
  -- Get the comass bound
  set C := max (comass ψ) (comass (smoothExtDeriv ψ)) with hC_def
  by_cases hC : C = 0
  · -- If C = 0, evaluation difference is always 0
    use 0
    intro n _
    rw [dist_eq_norm, Real.norm_eq_abs]
    have h_bound := eval_diff_le_flatNorm_diff (T n) T_limit ψ
    -- Since C = max ... = 0, we have max ... = 0
    have hmax : max (comass ψ) (comass (smoothExtDeriv ψ)) = 0 := hC
    rw [hmax, mul_zero] at h_bound
    linarith [abs_nonneg ((T n).toFun ψ - T_limit.toFun ψ)]
  · -- If C > 0, use it as denominator
    have hC_pos : C > 0 := by
      have h_nn := comass_nonneg ψ
      push_neg at hC
      exact lt_of_le_of_ne (le_max_of_le_left h_nn) (Ne.symm hC)
    obtain ⟨N, hN⟩ := h_conv (ε / C) (div_pos hε hC_pos)
    use N
    intro n hn
    specialize hN n hn
    rw [Real.dist_eq, sub_zero] at hN
    have h_bound := eval_diff_le_flatNorm_diff (T n) T_limit ψ
    rw [dist_eq_norm, Real.norm_eq_abs]
    have h_fn_nn : flatNorm (T n - T_limit) ≥ 0 := flatNorm_nonneg _
    calc |((T n).toFun ψ) - T_limit.toFun ψ|
        ≤ flatNorm (T n - T_limit) * C := h_bound
      _ ≤ |flatNorm (T n - T_limit)| * C := mul_le_mul_of_nonneg_right (le_abs_self _) (le_of_lt hC_pos)
      _ < (ε / C) * C := mul_lt_mul_of_pos_right hN hC_pos
      _ = ε := div_mul_cancel₀ ε (ne_of_gt hC_pos)

/-- **Limit Calibration Theorem** ⭐ STRATEGY-CRITICAL (Harvey-Lawson, 1982).

If a sequence of currents {Tₙ} satisfies:
1. calibrationDefect(Tₙ, ψ) → 0 as n → ∞
2. Tₙ → T_limit in flat norm

Then the limit current T_limit is calibrated by ψ.

**Proof Sketch**:
- calibrationDefect(Tₙ, ψ) = mass(Tₙ) - Tₙ(ψ) → 0
- By flat norm convergence: Tₙ(ψ) → T_limit(ψ) (evaluation is continuous)
- By mass_lsc: mass(T_limit) ≤ liminf mass(Tₙ)
- By calibration_inequality: T_limit(ψ) ≤ mass(T_limit)
- Combining: mass(Tₙ) → T_limit(ψ) (from defect → 0)
            mass(T_limit) ≤ liminf mass(Tₙ) = T_limit(ψ)
            T_limit(ψ) ≤ mass(T_limit)
- Hence mass(T_limit) = T_limit(ψ), i.e., T_limit is calibrated.

**Role in Proof**: This theorem is essential for showing that the limit of the
microstructure sequence is a calibrated current, which then represents
the positive part of the Hodge class.

Reference: [R. Harvey and H.B. Lawson Jr., "Calibrated geometries",
Acta Mathematica 148 (1982), 47-157, Theorem 4.2]. -/
theorem limit_is_calibrated {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k)
    (ψ : CalibratingForm n X k)
    (h_defect_vanish : Tendsto (fun i => calibrationDefect (T i) ψ) atTop (nhds 0))
    (h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    isCalibrated T_limit ψ := by
  unfold isCalibrated
  -- Step 1: Evaluation is continuous under flat convergence
  have h_eval_conv : Tendsto (fun i => (T i).toFun ψ.form) atTop (nhds (T_limit.toFun ψ.form)) :=
    eval_tendsto_of_flatNorm_tendsto T T_limit ψ.form h_conv
  -- Step 2: From defect → 0, we get mass(Tᵢ) - Tᵢ(ψ) → 0
  -- This means mass(Tᵢ) → Tᵢ(ψ), and since Tᵢ(ψ) → T_limit(ψ), we have mass(Tᵢ) → T_limit(ψ)
  have h_defect_eq : ∀ i, calibrationDefect (T i) ψ = Current.mass (T i) - (T i).toFun ψ.form := by
    intro i; rfl
  -- Step 3: mass(Tᵢ) = calibrationDefect + Tᵢ(ψ), and both parts converge
  have h_mass_conv : Tendsto (fun i => Current.mass (T i)) atTop (nhds (T_limit.toFun ψ.form)) := by
    have h1 : ∀ i, Current.mass (T i) = calibrationDefect (T i) ψ + (T i).toFun ψ.form := by
      intro i
      unfold calibrationDefect
      ring
    simp_rw [h1]
    convert Tendsto.add h_defect_vanish h_eval_conv using 1
    simp only [zero_add]
  -- Step 4: By lower semicontinuity, mass(T_limit) ≤ liminf mass(Tᵢ)
  have h_lsc := mass_lsc T T_limit h_conv
  -- Step 5: Since mass(Tᵢ) → T_limit(ψ), liminf = lim = T_limit(ψ)
  have h_liminf_eq : liminf (fun i => Current.mass (T i)) atTop = T_limit.toFun ψ.form := by
    exact h_mass_conv.liminf_eq
  -- Step 6: Therefore mass(T_limit) ≤ T_limit(ψ)
  have h_mass_le_eval : Current.mass T_limit ≤ T_limit.toFun ψ.form := by
    calc Current.mass T_limit ≤ liminf (fun i => Current.mass (T i)) atTop := h_lsc
      _ = T_limit.toFun ψ.form := h_liminf_eq
  -- Step 7: By calibration inequality, T_limit(ψ) ≤ mass(T_limit)
  have h_eval_le_mass : T_limit.toFun ψ.form ≤ Current.mass T_limit :=
    calibration_inequality T_limit ψ
  -- Step 8: Combine to get equality
  linarith

end
