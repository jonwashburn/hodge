import Hodge.Analytic.IntegralCurrents
import Hodge.Analytic.FlatNorm
import Hodge.Analytic.Norms
import Hodge.Kahler.TypeDecomposition
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Calibration Theory

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
  is_closed : isClosed form
  comass_le_one : comass form ≤ 1

/-! ## Kähler Calibration -/

/-- **Wirtinger Inequality** (Harvey-Lawson 1982). -/
axiom wirtinger_comass_bound (p : ℕ) :
    comass ((1 / (p.factorial : ℂ)) • omegaPow n X p) ≤ 1

/-- The Kähler calibration ω^p/p! as a 2p-form. -/
def KählerCalibration (p : ℕ) : CalibratingForm n X (2 * p) where
  form := (1 / (p.factorial : ℂ)) • omegaPow n X p
  is_closed := isClosed_omegaPow_scaled p
  comass_le_one := wirtinger_comass_bound p

/-! ## Calibration and Mass -/

/-- A current T is calibrated by ψ if T(ψ) achieves the mass. -/
def isCalibrated {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) : Prop :=
  Current.mass T = T.toFun ψ.form

/-- **Calibration Inequality** (Harvey-Lawson, 1982).
    For any current T and calibrating form ψ, the evaluation of T on ψ is bounded
    by the mass of T. This is the fundamental inequality of calibration theory.
    Reference: [R. Harvey and H.B. Lawson Jr., "Calibrated geometries", 1982]. -/
axiom calibration_inequality {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) :
    T.toFun ψ.form ≤ Current.mass T

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
    If a current T is a difference of a calibrated current S and an error current G,
    then the calibration defect of T is bounded by twice the mass of G. -/
axiom spine_theorem {k : ℕ} (T S G : Current n X k) (ψ : CalibratingForm n X k)
    (_h_decomp : T = S - G) (_h_calib : isCalibrated S ψ) :
    calibrationDefect T ψ ≤ 2 * Current.mass G

/-- **Lower Semicontinuity of Mass** (Federer-Fleming, 1960).
    The mass functional is lower semicontinuous with respect to the flat norm topology. -/
axiom mass_lsc {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k) :
    Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0) →
    Current.mass T_limit ≤ liminf (fun i => Current.mass (T i)) atTop

/-- **Limit Calibration Theorem** (Harvey-Lawson, 1982).
    If a sequence of currents has calibration defect tending to zero and
    converges in flat norm, then the limit current is calibrated.
    Reference: [R. Harvey and H.B. Lawson Jr., "Calibrated geometries", 1982]. -/
theorem limit_is_calibrated {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k)
    (ψ : CalibratingForm n X k)
    (h_defect_vanish : Tendsto (fun i => calibrationDefect (T i) ψ) atTop (nhds 0))
    (h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    isCalibrated T_limit ψ := by
  -- Use definition of isCalibrated: mass T_limit = T_limit ψ.form
  unfold isCalibrated
  
  -- 1. mass T_limit ≤ liminf (mass (T i)) by mass_lsc
  have h_mass_lsc := mass_lsc T T_limit h_conv
  
  -- 2. (T i) ψ.form → T_limit ψ.form by flat norm convergence
  have h_eval_conv := tendsto_eval_of_flat_conv ψ.form h_conv
  
  -- 3. mass (T i) = (T i) ψ.form + calibrationDefect (T i) ψ
  have h_mass_eq : ∀ i, Current.mass (T i) = (T i).toFun ψ.form + calibrationDefect (T i) ψ := by
    intro i; unfold calibrationDefect; linarith
    
  -- 4. liminf (mass (T i)) = liminf ((T i) ψ.form + defect)
  -- Since the sequence converges, liminf = limit
  have h_sum_conv : Tendsto (fun i => (T i).toFun ψ.form + calibrationDefect (T i) ψ) atTop 
      (nhds (T_limit.toFun ψ.form + 0)) := by
    apply Tendsto.add h_eval_conv h_defect_vanish
  rw [add_zero] at h_sum_conv
  
  have h_liminf_mass : liminf (fun i => Current.mass (T i)) atTop = T_limit.toFun ψ.form := by
    apply Tendsto.liminf_eq
    simp_rw [h_mass_eq]
    exact h_sum_conv
    
  -- 5. Conclusion: mass T_limit ≤ T_limit ψ.form and T_limit ψ.form ≤ mass T_limit
  apply le_antisymm
  · rw [← h_liminf_mass]
    exact h_mass_lsc
  · exact calibration_inequality T_limit ψ

end
