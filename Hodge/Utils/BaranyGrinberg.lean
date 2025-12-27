import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Order.Round

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
    simp [f, n]
    constructor
    · linarith [Int.floor_le (a i)]
    · linarith [Int.lt_floor_add_one (a i)]
  let S := ∑ i, f i
  let K := (Int.round S).toNat
  -- Since 0 ≤ f i < 1, 0 ≤ S < card ι.
  have hS_range : 0 ≤ S ∧ S < Fintype.card ι := by
    constructor
    · apply sum_nonneg; intro i _; exact (hf i).1
    · apply sum_lt_card_max
      · exact Fintype.card_pos_iff.mpr inferInstance
      · intro i _; exact (hf i).2
  
  -- We need to choose K indices to round up.
  -- 0 ≤ round S ≤ card ι.
  have hK : (Int.round S) ≤ Fintype.card ι := by
    have : S < Fintype.card ι := hS_range.2
    linarith [Int.round_le S]
  have hK_pos : 0 ≤ Int.round S := by
    have : 0 ≤ S := hS_range.1
    linarith [Int.le_round S]
  
  let s_univ := (univ : Finset ι)
  obtain ⟨s, hs_sub, hs_card⟩ := s_univ.exists_subset_card_eq (by 
    rw [card_univ]
    exact Int.toNat_le_toNat hK)
  
  let ε := fun i => if i ∈ s then n i + 1 else n i
  use ε
  constructor
  · intro i
    by_cases hi : i ∈ s
    · right
      simp [ε, hi, n]
      rw [Int.ceil_eq_floor_add_one]
      intro h_int
      have : f i = 0 := by
        simp [f, n, h_int]
      -- if f i = 0, then floor = ceil, so both are ok.
      -- wait, if f i = 0, then ceil (a i) = floor (a i).
      -- So n i + 1 is actually not ceil (a i).
      -- But we can pick ε i = n i in that case.
      -- Let's adjust the construction of s to only include indices where f i > 0 if possible.
      sorry
    · left
      simp [ε, hi, n]
  · sorry
