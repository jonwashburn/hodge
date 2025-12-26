/-!
# Track B.6: Calibration Theory

This file defines calibrating forms and calibrated currents,
with the key theorems relating calibration to mass minimization.

## Contents
- Calibrating form definition
- Calibrated current definition
- Spine theorem (mass defect bound)
- Limit calibration theorem

## Status
- [x] Define calibrating form
- [x] Define calibrated current
- [x] Prove spine theorem
- [ ] Prove limit calibration (has sorry)
-/

import Hodge.Analytic.IntegralCurrents
import Hodge.Analytic.FlatNorm
import Hodge.Classical.FedererFleming

noncomputable section

open Classical Filter

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [ProjectiveComplexManifold n X] [KahlerStructure n X]

/-! ## Calibrating Forms -/

/-- A calibrating form is a closed form with comass ≤ 1.
Such forms can be used to bound the mass of currents from below. -/
structure CalibratingForm (k : ℕ) where
  /-- The underlying differential form -/
  form : SmoothForm n X k
  /-- The form is closed: dψ = 0 -/
  is_closed : isClosed form
  /-- The comass is at most 1 -/
  comass_le_one : comass form ≤ 1

/-! ## Calibrated Currents -/

/-- A current T is calibrated by ψ if mass(T) = T(ψ).
This means T achieves the calibration inequality as an equality. -/
def isCalibrated {k : ℕ}
    (T : Current n X k) (ψ : CalibratingForm k) : Prop :=
  T.mass = T ψ.form

/-- The calibration inequality: T(ψ) ≤ mass(T) for any calibrating form ψ. -/
theorem calibration_inequality {k : ℕ}
    (T : Current n X k) (ψ : CalibratingForm k) :
    T ψ.form ≤ T.mass := by
  -- By definition of mass as dual norm
  have h := Current.eval_le_mass T ψ.form ψ.comass_le_one
  exact le_of_abs_le h

/-- Calibrated currents are mass-minimizing in their homology class. -/
theorem calibrated_is_mass_minimizing {k : ℕ}
    (T : Current n X k) (ψ : CalibratingForm k)
    (h_calibrated : isCalibrated T ψ)
    (h_cycle : T.isCycle) :
    ∀ (S : Current n X k), S.isCycle → (S - T).boundary = 0 →
      T.mass ≤ S.mass := by
  -- If S is homologous to T (i.e., S - T = ∂Q for some Q),
  -- then S(ψ) = T(ψ) (because ψ is closed).
  -- So mass(T) = T(ψ) = S(ψ) ≤ mass(S).
  sorry

/-! ## Calibration Defect -/

/-- The calibration defect of a current with respect to a calibrating form.
This measures how far T is from being calibrated by ψ. -/
def calibrationDefect {k : ℕ}
    (T : Current n X k) (ψ : CalibratingForm k) : ℝ :=
  T.mass - T ψ.form

/-- The calibration defect is non-negative. -/
theorem calibrationDefect_nonneg {k : ℕ}
    (T : Current n X k) (ψ : CalibratingForm k) :
    calibrationDefect T ψ ≥ 0 := by
  unfold calibrationDefect
  linarith [calibration_inequality T ψ]

/-- A current is calibrated iff its calibration defect is zero. -/
theorem isCalibrated_iff_defect_zero {k : ℕ}
    (T : Current n X k) (ψ : CalibratingForm k) :
    isCalibrated T ψ ↔ calibrationDefect T ψ = 0 := by
  unfold isCalibrated calibrationDefect
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## Spine Theorem -/

/-- **The Spine Theorem** (Theorem 8.1/9.1 of the manuscript)

If T = S - G where S is calibrated by ψ, then the mass defect
of T is bounded by 2 · mass(G).

This is the key quantitative estimate linking the correction current G
to the calibration defect of the sum. -/
theorem spine_theorem {k : ℕ}
    (T S G : Current n X k) (ψ : CalibratingForm k)
    (h_cycle : T.isCycle)
    (h_decomp : T = S - G)
    (h_calib : isCalibrated S ψ) :
    calibrationDefect T ψ ≤ 2 * G.mass := by
  -- Proof:
  -- 1. mass(T) = mass(S - G) ≤ mass(S) + mass(G)  [triangle inequality]
  -- 2. T(ψ) = (S - G)(ψ) = S(ψ) - G(ψ)           [linearity]
  -- 3. Since S is calibrated: S(ψ) = mass(S)
  -- 4. |G(ψ)| ≤ mass(G)                           [calibration inequality]
  -- 5. defect = mass(T) - T(ψ)
  --           ≤ mass(S) + mass(G) - (mass(S) - G(ψ))
  --           = G(ψ) + mass(G)
  --           ≤ |G(ψ)| + mass(G)
  --           ≤ 2 · mass(G)

  unfold calibrationDefect
  unfold isCalibrated at h_calib

  -- Step 1: mass(T) ≤ mass(S) + mass(G)
  have h1 : T.mass ≤ S.mass + G.mass := by
    calc T.mass = (S - G).mass := by rw [h_decomp]
      _ = (S + -G).mass := by
        have : S - G = S + -G := rfl
        rw [this]
      _ ≤ S.mass + (-G).mass := Current.mass_add_le S (-G)
      _ = S.mass + G.mass := by rw [Current.mass_neg]

  -- Step 2: T(ψ) = S(ψ) - G(ψ)
  have h2 : T ψ.form = S ψ.form - G ψ.form := by
    rw [h_decomp]
    simp only [LinearMap.sub_apply]

  -- Step 3: Using calibration S(ψ) = mass(S)
  rw [h2, h_calib]

  -- Step 4: |G(ψ)| ≤ mass(G)
  have h4 : |G ψ.form| ≤ G.mass := Current.eval_le_mass G ψ.form ψ.comass_le_one

  -- Combine
  calc T.mass - (S.mass - G ψ.form)
      = T.mass - S.mass + G ψ.form := by ring
    _ ≤ (S.mass + G.mass) - S.mass + G ψ.form := by linarith [h1]
    _ = G.mass + G ψ.form := by ring
    _ ≤ G.mass + |G ψ.form| := by linarith [le_abs_self (G ψ.form)]
    _ ≤ G.mass + G.mass := by linarith [h4]
    _ = 2 * G.mass := by ring

/-! ## Limit Calibration -/

/-- **Limit Calibration Theorem**

If the calibration defects of a sequence T_n tend to zero and
T_n converges in flat norm to T_limit, then T_limit is calibrated.

This is the key theorem for extracting calibrated limits from
almost-calibrated sequences. -/
theorem limit_is_calibrated {k : ℕ}
    (T : ℕ → Current n X k) (T_limit : Current n X k)
    (ψ : CalibratingForm k)
    (h_cycle : ∀ n, (T n).isCycle)
    (h_defect_vanish : Tendsto (fun n => calibrationDefect (T n) ψ) atTop (nhds 0))
    (h_conv : Tendsto (fun n => flatNorm (T n - T_limit)) atTop (nhds 0)) :
    isCalibrated T_limit ψ := by
  -- Proof:
  -- 1. By continuity of pairing, T_n(ψ) → T_limit(ψ)
  -- 2. Since defect = mass - pairing → 0 and pairing → T_limit(ψ),
  --    we have mass(T_n) → T_limit(ψ)
  -- 3. By lower semicontinuity of mass, mass(T_limit) ≤ liminf mass(T_n) = T_limit(ψ)
  -- 4. By calibration inequality, mass(T_limit) ≥ T_limit(ψ)
  -- 5. Therefore mass(T_limit) = T_limit(ψ), i.e., T_limit is calibrated.

  -- Step 1: Pairing converges
  have h1 : Tendsto (fun n => (T n) ψ.form) atTop (nhds (T_limit ψ.form)) := by
    -- flat_norm (T_n - T_limit) → 0 implies weak convergence
    -- |(T_n - T_limit)(ψ)| ≤ flat_norm(T_n - T_limit) * C
    rw [tendsto_iff_norm_tendsto_zero]
    simp only [sub_zero, norm_eq_abs, ← LinearMap.sub_apply]
    let C := max (comass ψ.form) (comass (extDeriv ψ.form))
    have h_bound : ∀ n, |(T n - T_limit) ψ.form| ≤ flatNorm (T n - T_limit) * C :=
      fun n => eval_le_flatNorm (T n - T_limit) ψ.form

    -- Since flatNorm (T n - T_limit) → 0, the right side → 0
    have h_zero : Tendsto (fun n => flatNorm (T n - T_limit) * C) atTop (nhds (0 * C)) :=
      Tendsto.mul_const C h_conv
    rw [zero_mul] at h_zero

    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) h_zero (fun n => abs_nonneg _) h_bound

  -- Step 2: Mass converges to T_limit(ψ)
  have h2 : Tendsto (fun n => (T n).mass) atTop (nhds (T_limit ψ.form)) := by
    -- mass = defect + pairing, defect → 0, pairing → T_limit(ψ)
    have h_sum : (fun n => (T n).mass) = fun n =>
        calibrationDefect (T n) ψ + (T n) ψ.form := by
      ext n; unfold calibrationDefect; ring
    rw [h_sum]
    exact Tendsto.add h_defect_vanish h1

  -- Step 3: Lower semicontinuity
  have h3 : T_limit.mass ≤ T_limit ψ.form := by
    -- Lower semicontinuity of mass: mass(T_limit) ≤ liminf mass(T_n)
    -- Since mass(T_n) converges to T_limit(ψ), the liminf is the limit.
    sorry -- Needs LSC lemma for mass norm

  -- Step 4: Calibration inequality (other direction)
  have h4 : T_limit ψ.form ≤ T_limit.mass :=
    calibration_inequality T_limit ψ

  -- Step 5: Equality
  unfold isCalibrated
  linarith

end
