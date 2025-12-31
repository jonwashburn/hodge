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

/-- **Wirtinger Inequality** (Harvey-Lawson 1982). -/
axiom wirtinger_comass_bound (p : ℕ) :
    comass ((1 / (p.factorial : ℂ)) • kahlerPow (n := n) (X := X) p) ≤ 1

/-- The Kähler calibration ω^p/p! as a 2p-form. -/
def KählerCalibration (p : ℕ) : CalibratingForm n X (2 * p) where
  form := (1 / (p.factorial : ℂ)) • kahlerPow p
  is_closed := IsFormClosed_omegaPow_scaled p
  comass_le_one := wirtinger_comass_bound p

/-! ## Calibration and Mass -/

/-- A current T is calibrated by ψ if T(ψ) achieves the mass. -/
def isCalibrated {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) : Prop :=
  Current.mass T = T.toFun ψ.form

/-- **Calibration Inequality** (Harvey-Lawson, 1982).
    For any current T and calibrating form ψ, the evaluation of T on ψ is bounded
    by the mass of T. This is the fundamental inequality of calibration theory.
    Reference: [R. Harvey and H.B. Lawson Jr., "Calibrated geometries", 1982].

    Proof: By eval_le_mass, |T(ψ)| ≤ mass(T) * comass(ψ).
    Since comass(ψ) ≤ 1 for a calibrating form, |T(ψ)| ≤ mass(T).
    Therefore T(ψ) ≤ |T(ψ)| ≤ mass(T). -/
theorem calibration_inequality {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) :
    T.toFun ψ.form ≤ Current.mass T := by
  have h1 : |T.toFun ψ.form| ≤ Current.mass T * comass ψ.form := eval_le_mass T ψ.form
  have h2 : comass ψ.form ≤ 1 := ψ.comass_le_one
  have h3 : Current.mass T * comass ψ.form ≤ Current.mass T * 1 := by
    apply mul_le_mul_of_nonneg_left h2 (Current.mass_nonneg T)
  calc T.toFun ψ.form
      ≤ |T.toFun ψ.form| := le_abs_self _
    _ ≤ Current.mass T * comass ψ.form := h1
    _ ≤ Current.mass T * 1 := h3
    _ = Current.mass T := mul_one _

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
    then the calibration defect of T is bounded by twice the mass of G.

    Proof: Let T = S - G where S is calibrated.
    - defect(T) = mass(T) - T(ψ)
    - mass(T) = mass(S - G) ≤ mass(S) + mass(G) (triangle inequality + mass_neg)
    - T(ψ) = S(ψ) - G(ψ) ≥ S(ψ) - mass(G) (by calibration_inequality on G)
    - Since S is calibrated: mass(S) = S(ψ)
    - defect(T) ≤ (mass(S) + mass(G)) - (S(ψ) - mass(G)) = 2 * mass(G) -/
theorem spine_theorem {k : ℕ} (T S G : Current n X k) (ψ : CalibratingForm n X k)
    (h_decomp : T = S - G) (h_calib : isCalibrated S ψ) :
    calibrationDefect T ψ ≤ 2 * Current.mass G := by
  unfold calibrationDefect
  -- T = S - G, so mass(T) ≤ mass(S) + mass(G) and T(ψ) = S(ψ) - G(ψ)
  have h_mass_T : Current.mass T ≤ Current.mass S + Current.mass G := by
    rw [h_decomp]
    calc Current.mass (S - G)
        = Current.mass (S + -G) := rfl
      _ ≤ Current.mass S + Current.mass (-G) := Current.mass_add_le S (-G)
      _ = Current.mass S + Current.mass G := by rw [Current.mass_neg]
  have h_eval_T : T.toFun ψ.form = S.toFun ψ.form - G.toFun ψ.form := by
    rw [h_decomp]
    simp only [Current.add_curr, Current.neg_curr]
    ring
  -- Since S is calibrated: mass(S) = S(ψ)
  have h_calib_eq : Current.mass S = S.toFun ψ.form := h_calib
  -- G(ψ) ≤ mass(G) by calibration inequality
  have h_G_bound : G.toFun ψ.form ≤ Current.mass G := calibration_inequality G ψ
  -- Combine: defect(T) = mass(T) - T(ψ) ≤ (mass(S) + mass(G)) - (S(ψ) - mass(G))
  calc Current.mass T - T.toFun ψ.form
      ≤ (Current.mass S + Current.mass G) - T.toFun ψ.form := by linarith
    _ = (Current.mass S + Current.mass G) - (S.toFun ψ.form - G.toFun ψ.form) := by rw [h_eval_T]
    _ = (Current.mass S - S.toFun ψ.form) + Current.mass G + G.toFun ψ.form := by ring
    _ = 0 + Current.mass G + G.toFun ψ.form := by rw [h_calib_eq]; ring_nf
    _ = Current.mass G + G.toFun ψ.form := by ring
    _ ≤ Current.mass G + Current.mass G := by linarith
    _ = 2 * Current.mass G := by ring

/-- **Lower Semicontinuity of Mass** (Federer-Fleming, 1960).
    The mass functional is lower semicontinuous with respect to the flat norm topology. -/
axiom mass_lsc {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k) :
    Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0) →
    Current.mass T_limit ≤ liminf (fun i => Current.mass (T i)) atTop

/-- **Limit Calibration Theorem** (Harvey-Lawson, 1982).
    If a sequence of currents has calibration defect tending to zero and
    converges in flat norm, then the limit current is calibrated.
    Reference: [R. Harvey and H.B. Lawson Jr., "Calibrated geometries", 1982]. -/
axiom limit_is_calibrated {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k)
    (ψ : CalibratingForm n X k)
    (_h_defect_vanish : Tendsto (fun i => calibrationDefect (T i) ψ) atTop (nhds 0))
    (_h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    isCalibrated T_limit ψ

end
