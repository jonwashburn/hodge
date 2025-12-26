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
- [x] Prove limit calibration
-/

import Hodge.Analytic.IntegralCurrents
import Hodge.Analytic.FlatNorm
import Hodge.Classical.FedererFleming

noncomputable section

open Classical Filter

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]

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

/-- **Definition: Kähler Calibration**
The p-th power of the Kähler form (normalized) is a calibrating form.
Reference: [Harvey-Lawson, 1982]. -/
def KählerCalibration (k : ℕ) [K : KahlerManifold n X] : CalibratingForm k where
  form := match k % 2 with
    | 0 => (1 / Nat.factorial (k / 2) : ℝ) • (omegaPow (k / 2))
    | _ => 0 -- Only even degrees are calibrated by Kähler powers
  is_closed := by
    -- ω^p is closed because ω is closed.
    cases h_parity : k % 2
    · -- k is even, k = 2p
      let p := k / 2
      induction p with
      | zero =>
          unfold omegaPow
          -- L^0 = 1, d(1) = 0
          sorry -- Need d(1) = 0
      | succ p' ih =>
          unfold omegaPow
          rw [d_wedge]
          -- d(ω ∧ ω^p) = dω ∧ ω^p + (-1)^2 ω ∧ d(ω^p)
          -- dω = 0 and d(ω^p) = 0 (by IH)
          sorry -- Need to handle the coercion and dω = 0
    · -- k is odd, form is 0
      simp only [extDeriv, map_zero]
      sorry
  comass_le_one := by
    -- Wirtinger's inequality: comass(ω^p / p!) ≤ 1.
    -- Equality holds at every point where the tangent space is a complex subspace.
    cases h_parity : k % 2
    · -- k is even, k = 2p
      let p := k / 2
      -- By Wirtinger's theorem, the comass of ω^p/p! is exactly 1.
      -- Proof sketch:
      -- 1. Pointwise, ω is a sum of dz_i ∧ dz̄_i.
      -- 2. ω^p/p! is a sum of products of dz_i ∧ dz̄_i.
      -- 3. The maximum value of this form on unit p-planes is achieved on complex p-planes.
      -- 4. For a complex p-plane, the value is exactly 1.
      sorry
    · -- k is odd, form is 0
      simp only [comass_zero]
      exact zero_le_one

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

/-- **Calibrated currents are mass-minimizing in their homology class.**
If T is calibrated by ψ and S is homologous to T, then mass(T) ≤ mass(S).
Reference: [Harvey-Lawson, "Calibrated Geometries", Acta Math 1982]. -/
theorem calibrated_is_mass_minimizing {k : ℕ}
    (T : Current n X k) (ψ : CalibratingForm k)
    (h_calibrated : isCalibrated T ψ)
    (h_cycle : T.isCycle) :
    ∀ (S : Current n X k), S.isCycle → (∃ Q, S - T = Q.boundary) →
      T.mass ≤ S.mass := by
  intro S hS_cycle ⟨Q, hST⟩
  -- 1. mass(T) = T(ψ) [since T is calibrated by ψ]
  -- 2. S(ψ) - T(ψ) = (S - T)(ψ) = ∂Q(ψ) = Q(dψ) [by duality]
  -- 3. Since ψ is closed, dψ = 0, so S(ψ) = T(ψ).
  -- 4. By calibration inequality, T(ψ) = S(ψ) ≤ mass(S).
  -- 5. Thus mass(T) ≤ mass(S).
  unfold isCalibrated at h_calibrated
  rw [h_calibrated]
  have h_pair : S ψ.form - T ψ.form = (S - T) ψ.form := rfl
  rw [hST] at h_pair
  have h_duality : Q.boundary ψ.form = Q (extDeriv ψ.form) := rfl
  rw [h_duality, ψ.is_closed, LinearMap.map_zero] at h_pair
  have h_eq : S ψ.form = T ψ.form := by linarith
  rw [← h_eq]
  exact calibration_inequality S ψ

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

/-- **Theorem: Lower Semicontinuity of Mass**
The mass norm is lower semicontinuous with respect to the flat norm topology.
Proof:
1. Mass is the dual norm to comass.
2. The mass of T is the supremum of evaluations |T(ψ)| for comass(ψ) ≤ 1.
3. Each evaluation T ↦ |T(ψ)| is continuous in the weak-* topology.
4. The supremum of continuous functions is lower semicontinuous.
5. Flat norm convergence implies weak-* convergence.
Reference: [Federer, "Geometric Measure Theory", 1969]. -/
theorem mass_lsc {k : ℕ} (T : ℕ → Current n X k) (T_limit : Current n X k) :
    Tendsto (fun n => flatNorm (T n - T_limit)) atTop (nhds 0) →
    T_limit.mass ≤ liminf (fun n => (T n).mass) atTop := by
  intro h_conv
  -- 1. mass T = sup { |T ψ| : comass ψ ≤ 1 }
  -- 2. Each pairing T ↦ T ψ is continuous in flat norm if comass(dψ) is also bounded.
  --    For a fixed smooth form ψ, |(T_n - T_limit) ψ| ≤ flatNorm(T_n - T_limit) * C.
  -- 3. Since T_n(ψ) → T_limit(ψ), and T_n(ψ) ≤ mass(T_n),
  --    we have T_limit(ψ) = lim T_n(ψ) ≤ liminf mass(T_n).
  -- 4. Taking the supremum over all ψ with comass ≤ 1 gives the result.
  unfold Current.mass
  apply Real.le_liminf_of_le
  · -- Pairing continuity
    intro ψ hψ
    -- For smooth forms on a compact manifold X, comass(dψ) is always bounded.
    let C := max (comass ψ) (comass (extDeriv ψ))
    have h_pair : Tendsto (fun n => (T n) ψ) atTop (nhds (T_limit ψ)) := by
      rw [tendsto_iff_norm_tendsto_zero]
      simp only [sub_zero, norm_eq_abs, ← LinearMap.sub_apply]
      have h_bound : ∀ n, |(T n - T_limit) ψ| ≤ flatNorm (T n - T_limit) * C :=
        fun n => eval_le_flatNorm (T n - T_limit) ψ
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds)
        (Tendsto.mul_const C h_conv) (fun n => abs_nonneg _) h_bound
    -- Thus T_limit(ψ) = lim T_n(ψ)
    have : T_limit ψ ≤ liminf (fun n => (T n) ψ) atTop := h_pair.liminf_eq.le
    -- And T_n(ψ) ≤ mass(T_n)
    have h_mass_n : ∀ n, (T n) ψ ≤ (T n).mass := fun n => (T n).le_opNorm ψ
    exact le_trans this (Real.liminf_le_liminf (fun n => h_mass_n n))
  · -- mass is non-negative
    intro n; apply Current.mass_nonneg

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
    have h_lsc := mass_lsc T T_limit h_conv
    have h_lim := h2.liminf_eq
    rw [← h_lim]
    exact h_lsc

  -- Step 4: Calibration inequality (other direction)
  have h4 : T_limit ψ.form ≤ T_limit.mass :=
    calibration_inequality T_limit ψ

  -- Step 5: Equality
  unfold isCalibrated
  linarith


end
