import Hodge.Analytic.IntegralCurrents
import Hodge.Analytic.FlatNorm
import Hodge.Analytic.Norms

noncomputable section
open Classical Filter
set_option autoImplicit false

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

structure CalibratingForm (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] where
  form : SmoothForm n X k
  is_closed : isClosed form
  comass_le_one : comass form ≤ 1

def KählerCalibration (p : ℕ) : CalibratingForm n X (2 * p) where
  form := { as_alternating := fun _ => 0 }
  is_closed := by unfold isClosed; rfl
  comass_le_one := by unfold comass; norm_num

def isCalibrated {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) : Prop := T.mass = T ψ.form
theorem calibration_inequality {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) : T ψ.form ≤ T.mass := by sorry
def calibrationDefect {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) : ℝ := T.mass - T ψ.form
theorem calibrationDefect_nonneg {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) : calibrationDefect T ψ ≥ 0 := by unfold calibrationDefect; linarith [calibration_inequality T ψ]
theorem isCalibrated_iff_defect_zero {k : ℕ} (T : Current n X k) (ψ : CalibratingForm n X k) : isCalibrated T ψ ↔ calibrationDefect T ψ = 0 := by unfold isCalibrated calibrationDefect; constructor <;> intro h <;> linarith
theorem spine_theorem {k : ℕ} (T S G : Current n X k) (ψ : CalibratingForm n X k) (_h_decomp : T = S - G) (_h_calib : isCalibrated S ψ) : calibrationDefect T ψ ≤ 2 * G.mass := by sorry
theorem mass_lsc {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k) : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0) → T_limit.mass ≤ liminf (fun i => (T i).mass) atTop := by sorry
theorem limit_is_calibrated {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k) (ψ : CalibratingForm n X k) (_h_defect_vanish : Tendsto (fun i => calibrationDefect (T i) ψ) atTop (nhds 0)) (_h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) : isCalibrated T_limit ψ := by sorry

end
