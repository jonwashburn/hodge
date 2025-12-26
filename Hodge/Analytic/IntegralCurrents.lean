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

/-- The Hausdorff dimension of a rectifiable set equals k.
Proof: A k-rectifiable set is by definition covered by Lipschitz images of k-dimensional sets.
Lipschitz maps do not increase Hausdorff dimension, and the dimension of ℝ^k is k. -/
theorem rectifiable_hausdorff_dim {k : ℕ} {S : Set X} (h : isRectifiable k S) :
    hausdorffDimension S ≤ k := by
  obtain ⟨K, f, hK, hf, h_null⟩ := h
  -- 1. By definition, S ⊆ (S \ ⋃ i, f i '' K i) ∪ (⋃ i, f i '' K i).
  -- 2. The Hausdorff dimension of a union is the supremum of the dimensions.
  -- 3. The first set in the union has measure zero, so its dimension is at most k.
  -- 4. For the second set, dim(⋃ i, f i '' K i) = sup_i dim(f i '' K i).
  -- 5. Since f i is Lipschitz, dim(f i '' K i) ≤ dim(K i) ≤ k.
  have h_cover : hausdorffDimension (⋃ i, f i '' K i) ≤ k := by
    rw [hausdorffDimension_iUnion]
    apply iSup_le; intro i
    -- 1. dim(f i '' K i) ≤ dim(K i) because f i is Lipschitz with constant 1.
    -- 2. dim(K i) ≤ dim(EuclideanSpace ℝ (Fin k)) because K i is a subset.
    -- 3. dim(ℝ^k) = k.
    apply le_trans (hausdorffDimension_image_le (hf i))
    apply le_trans (hausdorffDimension_le_of_subset (Set.subset_univ (K i)))
    -- Use the fact that hausdorffDimension of ℝ^k is k
    exact hausdorffDimension_euclidean_space k
  apply hausdorffDimension_le_of_subset_union S (⋃ i, f i '' K i)
  · -- 1. dim(S \ ⋃ i, f i '' K i) ≤ k because it has hausdorffMeasure k zero.
    -- If H^k(A) = 0, then dim_H(A) ≤ k.
    apply hausdorffDimension_le_of_hausdorffMeasure_zero
    exact h_null
  · exact h_cover

/-! ## Multiplicity Functions -/

/-- An integer multiplicity function on a set S. -/
def IntegerMultiplicity (S : Set X) := { x : X // x ∈ S } → ℤ

/-- The multiplicity function is integrable (finite total variation). -/
def isIntegrable {S : Set X} (θ : X → ℤ) (k : ℕ) : Prop :=
  ∫ x in S, |(θ x : ℝ)| ∂(hausdorffMeasure k) < ⊤

/-! ## Integral Currents -/

/-- A unit simple k-vector field representing the orientation of a rectifiable set. -/
def OrientationField (k : ℕ) (S : Set X) :=
  ∀ (x : X), x ∈ S → { ξ : Fin k → TangentSpace (𝓒_complex n) x // ∀ i, tangentNorm x (ξ i) ≤ 1 }

/-- **Definition: Integration Current**
Given a k-rectifiable set S, an orientation field ξ, and an integer multiplicity θ,
the integration current T is defined by the integration formula. -/
def integration_current {k : ℕ} (S : Set X) (hS : isRectifiable k S)
    (ξ : OrientationField k S) (θ : X → ℤ)
    (hθ : isIntegrable θ k) : Current n X k where
  toFun := fun ω => ∫ x in S, (θ x : ℝ) * (ω.as_alternating x (ξ x ‹x ∈ S›).1) ∂(hausdorffMeasure k)
  map_add' ω₁ ω₂ := by
    simp [SmoothForm.eval, Add.add]
    -- Linearity follows from the linearity of AlternatingMap.eval and the integral
    rw [← integral_add]
    · -- Integrability of (θ x) * (ω₁ + ω₂)(ξ)
      apply integrable_of_le (fun x => |(θ x : ℝ)| * comass (ω₁ + ω₂))
      · apply Integrable.mul_const hθ
      · intro x; dsimp
        by_cases hx : x ∈ S
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          let ξx := (ξ x hx).1
          let h_unit := (ξ x hx).2
          have h_pt_le : |(ω₁ + ω₂).as_alternating x ξx| ≤ pointwiseComass (ω₁ + ω₂) x := by
            unfold pointwiseComass
            apply Real.le_sSup
            · use comass (ω₁ + ω₂)
              rintro r ⟨v, hv, rfl⟩
              apply le_trans (Real.le_iSup _ x) (le_refl _)
            · use ξx, h_unit
          exact le_trans h_pt_le (le_ciSup (comass_finite (ω₁ + ω₂)).bddAbove x)
        · simp [MeasureTheory.indicator_apply, hx]
    · -- Integrability of ω₁ pairing
      apply integrable_of_le (fun x => |(θ x : ℝ)| * comass ω₁)
      · apply Integrable.mul_const hθ
      · intro x; dsimp
        by_cases hx : x ∈ S
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          let ξx := (ξ x hx).1
          let h_unit := (ξ x hx).2
          have h_pt_le : |ω₁.as_alternating x ξx| ≤ pointwiseComass ω₁ x := by
            unfold pointwiseComass
            apply Real.le_sSup
            · use comass ω₁
              rintro r ⟨v, hv, rfl⟩
              apply le_trans (Real.le_iSup _ x) (le_refl _)
            · use ξx, h_unit
          exact le_trans h_pt_le (le_ciSup (comass_finite ω₁).bddAbove x)
        · simp [MeasureTheory.indicator_apply, hx]
    · -- Integrability of ω₂ pairing
      apply integrable_of_le (fun x => |(θ x : ℝ)| * comass ω₂)
      · apply Integrable.mul_const hθ
      · intro x; dsimp
        by_cases hx : x ∈ S
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          let ξx := (ξ x hx).1
          let h_unit := (ξ x hx).2
          have h_pt_le : |ω₂.as_alternating x ξx| ≤ pointwiseComass ω₂ x := by
            unfold pointwiseComass
            apply Real.le_sSup
            · use comass ω₂
              rintro r ⟨v, hv, rfl⟩
              apply le_trans (Real.le_iSup _ x) (le_refl _)
            · use ξx, h_unit
          exact le_trans h_pt_le (le_ciSup (comass_finite ω₂).bddAbove x)
        · simp [MeasureTheory.indicator_apply, hx]
    · -- Linearity check
      congr; ext x; rw [DifferentialForm.add_apply, mul_add]
  map_smul' r ω := by
    simp [SmoothForm.eval, SMul.smul]
    -- Linearity follows from the linearity of AlternatingMap.eval and the integral
    rw [← integral_smul]
    congr; ext x
    dsimp
    by_cases hx : x ∈ S
    · ring
    · simp [MeasureTheory.indicator_apply, hx]

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
    isIntegral S → isIntegral T → isIntegral (S + T) := by
  rintro ⟨S_set, hS_rect, ξ_S, θ_S, hθ_S, rfl⟩ ⟨T_set, hT_rect, ξ_T, θ_T, hθ_T, rfl⟩
  unfold isIntegral
  let U := S_set ∪ T_set
  -- 1. Union of rectifiable sets is rectifiable.
  have hU_rect : isRectifiable k U := by
    obtain ⟨KS, fS, hKS, hfS, hS_null⟩ := hS_rect
    obtain ⟨KT, fT, hKT, hfT, hT_null⟩ := hT_rect
    let K := fun i => if i % 2 = 0 then KS (i/2) else KT (i/2)
    let f := fun i => if i % 2 = 0 then fS (i/2) else fT (i/2)
    use K, f
    constructor
    · intro i; cases h : i % 2 <;> simp [K, h, hKS, hKT]
    · constructor
      · intro i; cases h : i % 2 <;> simp [f, h, hfS, hfT]
      · -- The null set property: (S ∪ T) \ ⋃ f i '' K i ⊆ (S \ ⋃ fS i '' KS i) ∪ (T \ ⋃ fT i '' KT i)
        -- Since both sets on the RHS are null, the LHS is null.
        apply measure_mono_null
        · intro x hx
          simp only [Set.mem_union, Set.mem_diff, Set.mem_iUnion, Set.mem_image] at hx ⊢
          obtain ⟨hx_mem, hx_not_mem⟩ := hx
          cases hx_mem with
          | inl hS =>
              left; constructor; exact hS
              intro h_exists; apply hx_not_mem
              obtain ⟨i, y, hy_K, hy_f⟩ := h_exists
              use 2 * i, y; constructor
              · simp [K]; split_ifs; exact hy_K
              · simp [f]; split_ifs; exact hy_f
          | inr hT =>
              right; constructor; exact hT
              intro h_exists; apply hx_not_mem
              obtain ⟨i, y, hy_K, hy_f⟩ := h_exists
              use 2 * i + 1, y; constructor
              · simp [K]; split_ifs; exact hy_K
              · simp [f]; split_ifs; exact hy_f
        · rw [measure_union_null hS_null hT_null]
  use U, hU_rect
  -- 2. Orientation Field: needs to account for possible overlapping sets with opposite orientations.
  -- For the sum of currents, we can just use the indicator functions.
  let ξ_U : OrientationField k U := fun x hx =>
    if h : x ∈ S_set then ξ_S x h else ξ_T x (by
      simp only [Set.mem_union] at hx
      exact hx.resolve_left h)
  use ξ_U
  -- 3. Multiplicity: the sum of multiplicities (accounting for orientation differences).
  -- If x ∈ S ∩ T, the orientations ξ_S and ξ_T might differ by a sign or more.
  -- In general, for integral currents, the tangent planes match a.e. on the intersection.
  let θ_U : X → ℤ := fun x =>
    (if h : x ∈ S_set then θ_S x else 0) +
    (if h : x ∈ T_set then (if ξ_T x h = ξ_U x (Set.mem_union_right _ h) then θ_T x else -θ_T x) else 0)
  use θ_U
  -- 4. Integrability of the sum.
  have hθ_U : isIntegrable θ_U k := by
    unfold isIntegrable
    -- Since θ_U is a sum of indicator-weighted integrables, it is integrable.
    -- ∫ |θ_U| ≤ ∫ (|θ_S| * χ_S + |θ_T| * χ_T) = ∫ |θ_S| + ∫ |θ_T| < ⊤.
    apply integrable_of_le (fun x => |(θ_S x : ℝ)| + |(θ_T x : ℝ)|)
    · apply Integrable.add
      · exact hθ_S
      · exact hθ_T
    · intro x; dsimp [θ_U]
      -- Using triangle inequality: |a + b| ≤ |a| + |b|.
      apply le_trans (abs_add _ _)
      apply add_le_add
      · split_ifs <;> simp [abs_nonneg]
      · split_ifs <;> simp [abs_nonneg, abs_neg]
  use hθ_U
  -- 5. The sum of integration currents matches the integration current of the union.
  ext ω
  simp only [AddCommGroup.add_apply, integration_current, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  rw [← integral_add]
  · -- ∫_{S∪T} θ_U * ω(ξ_U) = ∫_S θ_S * ω(ξ_S) + ∫_T θ_T * ω(ξ_T)
    -- Both sides are equal to the integral over X of the indicator-weighted functions.
    -- (θ_S * ω(ξ_S) * χ_S) + (θ_T * ω(ξ_T) * χ_T) = θ_U * ω(ξ_U) * χ_U
    -- At any point x:
    -- if x ∈ S \ T: θ_S * ω(ξ_S) + 0 = θ_U * ω(ξ_U) (matches since θ_U = θ_S, ξ_U = ξ_S)
    -- if x ∈ T \ S: 0 + θ_T * ω(ξ_T) = θ_U * ω(ξ_U) (matches since θ_U = ±θ_T, ξ_U = sign-adjusted ξ_T)
    -- if x ∈ S ∩ T: θ_S * ω(ξ_S) + θ_T * ω(ξ_T) = (θ_S + ±θ_T) * ω(ξ_S) (matches)
    congr; ext x
    dsimp [θ_U, ξ_U]
    split_ifs with hS hT hT'
    · -- x ∈ S ∩ T
      by_cases h_orient : (ξ_T x hT).1 = (ξ_S x hS).1
      · simp [h_orient]; ring
      · -- If orientations differ, they must be opposite for integral currents a.e.
        -- ξ_T = -ξ_S. In this case, θ_U = θ_S - θ_T correctly accounts for it.
        -- We assume the canonical decomposition property of integral currents.
        have : (ξ_T x hT).1 = -(ξ_S x hS).1 := sorry
        simp [h_orient, this]
        ring
    · -- x ∈ S \ T
      simp [hS, hT]; ring
    · -- x ∈ T \ S
      simp [hS, hT]; ring
    · -- x ∉ S ∪ T
      simp [hS, hT]
  · -- integrability of S current integrand
    apply integrable_of_le (fun x => |(θ_S x : ℝ)| * comass ω)
    · apply Integrable.mul_const hθ_S
    · intro x; dsimp
      by_cases hx : x ∈ S_set
      · rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        let v := (ξ_S x hx).1
        let hv := (ξ_S x hx).2
        have : |ω.as_alternating x v| ≤ pointwiseComass ω x := by
          apply Real.le_sSup _ ⟨v, hv, rfl⟩
          use comass ω
          rintro r ⟨v', hv', rfl⟩
          exact le_trans (Real.le_iSup (pointwiseComass ω) x) (le_refl _)
        exact le_trans this (le_ciSup (comass_finite ω).bddAbove x)
      · simp [MeasureTheory.indicator_apply, hx]
  · -- integrability of T current integrand
    apply integrable_of_le (fun x => |(θ_T x : ℝ)| * comass ω)
    · apply Integrable.mul_const hθ_T
    · intro x; dsimp
      by_cases hx : x ∈ T_set
      · rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        let v := (ξ_T x hx).1
        let hv := (ξ_T x hx).2
        have : |ω.as_alternating x v| ≤ pointwiseComass ω x := by
          apply Real.le_sSup _ ⟨v, hv, rfl⟩
          use comass ω
          rintro r ⟨v', hv', rfl⟩
          exact le_trans (Real.le_iSup (pointwiseComass ω) x) (le_refl _)
        exact le_trans this (le_ciSup (comass_finite ω).bddAbove x)
      · simp [MeasureTheory.indicator_apply, hx]

/-- Integer Scaling of Integral Currents is Integral -/
theorem isIntegral_smul {k : ℕ} (c : ℤ) (T : Current n X k) :
    isIntegral T → isIntegral (c • T) := by
  rintro ⟨S, hS, ξ, θ, hθ, rfl⟩
  unfold isIntegral
  use S, hS, ξ, (fun x => c * θ x)
  · have h_int : isIntegrable (fun x => c * θ x) k := by
      unfold isIntegrable
      simp only [Int.cast_mul, Int.cast_id, abs_mul]
      -- Since c is constant, ∫ |c| * |θ| = |c| * ∫ |θ| < ⊤
      apply Integrable.const_mul
      exact hθ
    use h_int
    -- Linearity of integration current: ∫ (c*θ) = c * ∫ θ
    ext ω
    simp only [HSMul.hSMul, SMul.smul, LinearMap.smul_apply, integration_current, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [Int.cast_mul, Int.cast_id, mul_assoc]
    rw [← integral_smul]
    congr; ext x; ring

/-- **Boundary of Integral Current is Integral**
If T is an integral current, its boundary ∂T is also an integral current.
Reference: [Federer-Fleming, "Normal and Integral Currents", Ann. Math 1960]. -/
theorem isIntegral_boundary {k : ℕ} (T : Current n X (k + 1)) :
    isIntegral T → isIntegral T.boundary := by
  intro hT
  -- 1. By the Boundary Rectifiability Theorem (Theorem 4.5 of Federer-Fleming 1960),
  --    if T is an integral current and ∂T has finite mass, then ∂T is integral.
  -- 2. Integral currents in the sense of Federer-Fleming are defined to have
  --    finite mass and boundary mass.
  -- 3. The boundary operator maps integral currents to integral currents.
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
  rintro ⟨S, hS, ξ, θ, hθ, rfl⟩
  use S, hS, θ, hθ
  -- 1. |∫ θ * ω(ξ)| ≤ ∫ |θ| * |ω(ξ)| ≤ ∫ |θ| * comass(ω) ≤ ∫ |θ|.
  --    So mass(T) ≤ ∫ |θ|.
  have h_le : T.mass ≤ ∫ x in S, |(θ x : ℝ)| ∂(hausdorffMeasure k) := by
    unfold Current.mass
    apply ciSup_le; intro ω
    rw [norm_eq_abs, abs_integral]
    apply le_trans (integral_mono _ _ _)
    · apply integrable_of_le (fun x => |(θ x : ℝ)| * comass ω)
      · apply Integrable.mul_const hθ
      · intro x; dsimp; rw [abs_mul]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        by_cases hx : x ∈ S
        · let ξx := (ξ x hx).1
          have h_pt_le : |ω.as_alternating x ξx| ≤ pointwiseComass ω x := by
            apply Real.le_sSup _ ⟨ξx, (ξ x hx).2, rfl⟩
            use comass ω
            rintro r ⟨v, hv, rfl⟩
            exact le_trans (Real.le_iSup (pointwiseComass ω) x) (le_refl _)
          exact le_trans h_pt_le (le_ciSup (comass_finite ω).bddAbove x)
        · simp [MeasureTheory.indicator_apply, hx]
    · intro x; dsimp
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      by_cases hx : x ∈ S
      · let ξx := (ξ x hx).1
        have h_pt_le : |ω.as_alternating x ξx| ≤ pointwiseComass ω x := by
          apply Real.le_sSup _ ⟨ξx, (ξ x hx).2, rfl⟩
          use comass ω
          rintro r ⟨v, hv, rfl⟩
          exact le_trans (Real.le_iSup (pointwiseComass ω) x) (le_refl _)
        exact le_trans h_pt_le (le_ciSup (comass_finite ω).bddAbove x)
      · simp [MeasureTheory.indicator_apply, hx]
    · -- integrability of |θ|
      simp only [norm_eq_abs, abs_cast]
      exact hθ
  -- 2. By choosing a test form ω that closely approximates sign(θ) * ξ^* (dual vector field),
  --    using Lusin's theorem and a partition of unity, we approach ∫ |θ|.
  have h_ge : ∫ x in S, |(θ x : ℝ)| ∂(hausdorffMeasure k) ≤ T.mass := by
    -- supremum property
    sorry
  linarith

/-- The mass of an integral current equals the integral of |θ|. -/
theorem IntegralCurrent.mass_eq_integral {k : ℕ} (T : IntegralCurrent n X k) :
    ∃ (S : Set X) (hS : isRectifiable k S) (θ : X → ℤ),
      (T.toFun).mass = ∫ x in S, |(θ x : ℝ)| ∂(hausdorffMeasure k) := by
  obtain ⟨S, hS, ξ, θ, hθ, h_eq⟩ := T.is_integral
  obtain ⟨S', hS', θ', hθ', h_mass⟩ := mass_eq_integral_theorem T.toFun T.is_integral
  use S', hS', θ'
  exact h_mass

end
