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

/-- **Wirtinger Inequality** (Harvey-Lawson 1982).

The Wirtinger form ω^p/p! has comass at most 1 on any Kähler manifold.
This is the fundamental inequality that makes ω^p/p! a calibrating form.

**Proof Sketch**: For any complex p-plane V in the tangent space,
the pairing of ω^p/p! with the volume form of V equals 1 (Wirtinger's theorem).
For other p-planes, the pairing is strictly less than 1.
Hence the comass (supremum over all p-planes) equals 1.

Reference: [R. Harvey and H.B. Lawson Jr., "Calibrated geometries",
Acta Mathematica 148 (1982), 47-157, Theorem 2.3]. -/
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

/-- **Lower Semicontinuity of Mass** (Federer-Fleming, 1960).

The mass functional is lower semicontinuous with respect to the flat norm topology.
This means: if Tₙ → T in flat norm, then mass(T) ≤ liminf mass(Tₙ).

**Proof Sketch**: The mass is defined as sup{T(ω) : comass(ω) ≤ 1}.
For each test form ω, the evaluation T(ω) is continuous in T (w.r.t. flat norm).
The supremum of lower semicontinuous functions is lower semicontinuous.

Reference: [H. Federer and W.H. Fleming, "Normal and integral currents",
Annals of Mathematics 72 (1960), 458-520, Section 4.2]. -/
axiom mass_lsc {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k) :
    Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0) →
    Current.mass T_limit ≤ liminf (fun i => Current.mass (T i)) atTop

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
axiom limit_is_calibrated {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k)
    (ψ : CalibratingForm n X k)
    (_h_defect_vanish : Tendsto (fun i => calibrationDefect (T i) ψ) atTop (nhds 0))
    (_h_conv : Tendsto (fun i => flatNorm (T i - T_limit)) atTop (nhds 0)) :
    isCalibrated T_limit ψ

end
