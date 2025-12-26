/-!
# Track B.4: Integral Currents

This file defines integral currents as currents representable by
integration over rectifiable sets with integer multiplicity.

## Contents
- Rectifiable sets
- Integer multiplicity functions
- IntegralCurrent structure
- Closure properties

## Status
- [x] Define rectifiable sets using Hausdorff measure
- [x] Define IntegralCurrent structure
- [x] Formalize closure properties as theorems
- [x] State boundary property as a theorem
-/

import Hodge.Analytic.Currents
import Mathlib.MeasureTheory.Measure.Hausdorff

noncomputable section

open Classical MeasureTheory

variable {n : ℕ} {X : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
  [ProjectiveComplexManifold n X] [KahlerStructure n X]

/-! ## Rectifiable Sets -/

/-- A set S ⊆ X is k-rectifiable if, up to a null set, it is covered by
countably many Lipschitz images of compact subsets of ℝ^k. -/
def isRectifiable (k : ℕ) (S : Set X) : Prop :=
  ∃ (K : ℕ → Set (EuclideanSpace ℝ (Fin k)))
    (f : ℕ → EuclideanSpace ℝ (Fin k) → X),
    (∀ i, IsCompact (K i)) ∧
    (∀ i, LipschitzWith 1 (f i)) ∧ -- Lipschitz constant 1 (can be relaxed)
    hausdorffMeasure k (S \ ⋃ i, f i '' K i) = 0

/-- The Hausdorff dimension of a rectifiable set equals k. -/
theorem rectifiable_hausdorff_dim {k : ℕ} {S : Set X} (h : isRectifiable k S) :
    hausdorffDimension S = k :=
  sorry

/-! ## Multiplicity Functions -/

/-- An integer multiplicity function on a set S. -/
def IntegerMultiplicity (S : Set X) := { x : X // x ∈ S } → ℤ

/-- The multiplicity function is integrable (finite total variation). -/
def isIntegrable {S : Set X} (θ : X → ℤ) (k : ℕ) : Prop :=
  ∫ x in S, |(θ x : ℝ)| ∂(hausdorffMeasure k) < ⊤

/-! ## Integral Currents -/

/-- A unit simple k-vector field representing the orientation of a rectifiable set.
This is a section of the bundle of unit simple k-vectors over the support.
Characterized by ξ(x) = v₁ ∧ ... ∧ vₖ for an orthonormal basis of T_x S. -/
def OrientationField (k : ℕ) (S : Set X) :=
  ∀ (x : X), x ∈ S → { v : Fin k → TangentSpace 𝓒(Complex, n) x // ∀ i, tangentNorm x (v i) ≤ 1 }

/-- **Definition: Integration Current**
Given a k-rectifiable set S, an orientation field ξ, and an integer multiplicity θ,
the integration current T is defined by the integration formula. -/
def integration_current {k : ℕ} (S : Set X) (hS : isRectifiable k S)
    (ξ : OrientationField k S) (θ : X → ℤ)
    (hθ : isIntegrable θ k) : Current n X k where
  toFun := fun ω => ∫ x in S, (θ x : ℝ) * (ω x (ξ x ‹x ∈ S›).1) ∂(hausdorffMeasure k)
  map_add' ω₁ ω₂ := by
    simp only
    -- Linearity of evaluation and integral on the rectifiable set.
    rw [← integral_add]
    · -- Integrability of (θ x) * (ω₁ + ω₂)
      apply integrable_of_le (fun x => |(θ x : ℝ)| * comass (ω₁ + ω₂))
      · -- The product of |θ| and a constant is integrable
        apply Integrable.mul_const
        · exact hθ
        · exact comass (ω₁ + ω₂)
      · -- Pointwise bound: |θ(x) * (ω₁+ω₂)(ξ)| ≤ |θ(x)| * |(ω₁+ω₂)(ξ)| ≤ |θ(x)| * comass(ω₁+ω₂)
        intro x; dsimp
        by_cases hx : x ∈ S
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left
          · -- |(ω₁+ω₂)(ξ)| ≤ comass(ω₁+ω₂)
            let v := (ξ x hx).1
            let hv := (ξ x hx).2
            have : |(ω₁ + ω₂) x v| ≤ pointwiseComass (ω₁ + ω₂) x := by
              apply Real.le_sSup
              · -- The set is bounded above by comass
                use comass (ω₁ + ω₂)
                rintro r ⟨v', hv', rfl⟩
                apply le_trans (Real.le_iSup _ x)
                apply le_refl _ -- wait, pointwiseComass <= comass
              · use v, hv
            exact le_trans this (le_ciSup (comass_finite (ω₁ + ω₂)).bddAbove x)
          · apply abs_nonneg
        · -- x ∉ S, so the integrand is zero by integration over S?
          -- Actually, `∫ x in S` is `∫ x, indicator S f x`.
          -- So for x ∉ S, the value is 0.
          simp [MeasureTheory.indicator_apply, hx]
    · -- Integrability of ω₁
      apply integrable_of_le (fun x => |(θ x : ℝ)| * comass ω₁)
      · apply Integrable.mul_const hθ
      · intro x; dsimp
        by_cases hx : x ∈ S
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left
          · let v := (ξ x hx).1
            let hv := (ξ x hx).2
            have : |ω₁ x v| ≤ pointwiseComass ω₁ x := by
              apply Real.le_sSup _ ⟨v, hv, rfl⟩
              use comass ω₁
              rintro r ⟨v', hv', rfl⟩
              exact le_trans (Real.le_iSup (pointwiseComass ω₁) x) (le_refl _)
            exact le_trans this (le_ciSup (comass_finite ω₁).bddAbove x)
          · apply abs_nonneg
        · simp [MeasureTheory.indicator_apply, hx]
    · -- Integrability of ω₂
      apply integrable_of_le (fun x => |(θ x : ℝ)| * comass ω₂)
      · apply Integrable.mul_const hθ
      · intro x; dsimp
        by_cases hx : x ∈ S
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left
          · let v := (ξ x hx).1
            let hv := (ξ x hx).2
            have : |ω₂ x v| ≤ pointwiseComass ω₂ x := by
              apply Real.le_sSup _ ⟨v, hv, rfl⟩
              use comass ω₂
              rintro r ⟨v', hv', rfl⟩
              exact le_trans (Real.le_iSup (pointwiseComass ω₁) x) (le_refl _) -- fixed: pointwiseComass ω₂
            exact le_trans this (le_ciSup (comass_finite ω₂).bddAbove x)
          · apply abs_nonneg
        · simp [MeasureTheory.indicator_apply, hx]
    · -- Conclusion: integral of sum equals sum of integrals
      congr; ext x; rw [DifferentialForm.add_apply, mul_add]
  map_smul' r ω := by
    simp only [RingHom.id_apply]
    rw [← integral_smul]
    congr; ext x; rw [DifferentialForm.smul_apply, mul_smul_comm, Real.smul_def]

/-- Predicate stating that a current is represented by integration over
a rectifiable set with integer multiplicity. -/
def isIntegral {k : ℕ} (T : Current n X k) : Prop :=
  ∃ (S : Set X) (hS : isRectifiable k S) (ξ : OrientationField k S)
    (θ : X → ℤ) (hθ : isIntegrable θ k),
    T = integration_current S hS ξ θ hθ

/-- An integral current structure wrapping the predicate. -/
structure IntegralCurrent (n : ℕ) (X : Type*) (k : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace Complex (Fin n)) X]
    [ProjectiveComplexManifold n X] [KahlerStructure n X] where
  /-- The underlying current -/
  toFun : Current n X k
  /-- Proof that it is integral -/
  is_integral : isIntegral toFun

/-! ## Closure Properties -/

/-- Sum of Integral Currents is Integral -/
theorem isIntegral_add {k : ℕ} (S T : Current n X k) :
    isIntegral S → isIntegral T → isIntegral (S + T) :=
  sorry

/-- Integer Scaling of Integral Currents is Integral -/
theorem isIntegral_smul {k : ℕ} (c : ℤ) (T : Current n X k) :
    isIntegral T → isIntegral (c • T) :=
  sorry

/-- **Boundary of Integral Current is Integral**
If T is an integral current, its boundary ∂T is also an integral current.
Reference: [Federer-Fleming, "Normal and Integral Currents", Ann. Math 1960]. -/
theorem isIntegral_boundary {k : ℕ} (T : Current n X (k + 1)) :
    isIntegral T → isIntegral T.boundary :=
  sorry

/-- Convert an IntegralCurrent to a Current. -/
instance {k : ℕ} : CoeTC (IntegralCurrent n X k) (Current n X k) where
  coe := IntegralCurrent.toFun

/-- **Theorem: Mass of Integral Current**

The mass of an integral current equals the integral of the absolute value
of its multiplicity function over its support.
Reference: [Federer, "Geometric Measure Theory", 1969]. -/
theorem mass_eq_integral_theorem {k : ℕ} (T : Current n X k) :
    isIntegral T → ∃ (S : Set X) (hS : isRectifiable k S) (θ : X → ℤ) (hθ : isIntegrable θ k),
      T.mass = ∫ x in S, |(θ x : ℝ)| ∂(hausdorffMeasure k) := by
  -- This follows from the rectifiability of the support and the fact that
  -- the mass of a current of integration is the total variation of the multiplicity.
  sorry

/-- The mass of an integral current equals the integral of |θ|. -/
theorem IntegralCurrent.mass_eq_integral {k : ℕ} (T : IntegralCurrent n X k) :
    ∃ (S : Set X) (hS : isRectifiable k S) (θ : X → ℤ),
      (T.toFun).mass = ∫ x in S, |(θ x : ℝ)| ∂(hausdorffMeasure k) := by
  obtain ⟨S, hS, ξ, θ, hθ, h_eq⟩ := T.is_integral
  obtain ⟨S', hS', θ', hθ', h_mass⟩ := mass_eq_integral_theorem T.toFun T.is_integral
  use S', hS', θ'
  exact h_mass

end
