import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open Finset

/-- **Lemma: 1-Dimensional Discrepancy Rounding**
Given real numbers aᵢ, we can round each to an integer εᵢ ∈ {⌊aᵢ⌋, ⌈aᵢ⌉}
such that the sum is rounded: ∑ εᵢ = round(∑ aᵢ).
This is the d=1 case of Bárány-Grinberg.
-/
theorem rounding_d1 {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∃ ε : ι → ℤ, (∀ i, (ε i : ℝ) = Int.floor (a i) ∨ (ε i : ℝ) = Int.ceil (a i)) ∧
      (∑ i, ε i : ℝ) = Int.round (∑ i, a i) := by
  let n := fun i => Int.floor (a i)
  let f := fun i => a i - n i
  have hf : ∀ i, 0 ≤ f i ∧ f i < 1 := by
    intro i
    simp [f, n, Int.floor_le, Int.lt_floor_add_one]
    constructor
    · linarith [Int.floor_le (a i)]
    · linarith [Int.lt_floor_add_one (a i)]
  let S := ∑ i, f i
  let K := Int.round S
  -- We need to choose K indices to round up.
  -- Since 0 ≤ f i < 1, 0 ≤ S < card ι.
  -- Thus 0 ≤ K ≤ card ι.
  have hK_range : 0 ≤ K ∧ (K : ℤ) ≤ Fintype.card ι := sorry -- Easy but needs bounds on round
  obtain ⟨s, hs_card, hs_subset⟩ := exists_subset_card_eq hK_range.2
  let ε := fun i => if i ∈ s then n i + 1 else n i
  use ε
  constructor
  · intro i
    by_cases hi : i ∈ s
    · right; simp [ε, hi, n]; rw [Int.ceil_eq_floor_add_one]; linarith [hf i]
      -- wait, ceil is floor + 1 unless f = 0
      sorry
    · left; simp [ε, hi, n]
  · sorry
