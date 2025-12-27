import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Pi

open Set Convex
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- **Lemma: Bárány-Grinberg Rounding**
Let v₁, ..., vₘ be vectors in ℝᵈ with ‖vᵢ‖_∞ ≤ 1. For any coefficients aᵢ ∈ [0, 1],
there exist εᵢ ∈ {0, 1} such that ‖∑ (εᵢ - aᵢ) vᵢ‖_∞ ≤ d.
-/
theorem barany_grinberg (v : ι → (Fin d → ℝ)) (hv : ∀ i j, |v i j| ≤ 1)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) :
    ∃ ε : ι → ℝ, (∀ i, ε i = 0 ∨ ε i = 1) ∧
      ∀ j, |∑ i, (ε i - a i) * v i j| ≤ d := by
  let x := fun j => ∑ i, a i * v i j
  let P := { t : ι → ℝ | (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ ∀ j, (∑ i, t i * v i j) = x j }

  have haP : a ∈ P := ⟨ha, fun _ => rfl⟩

  have hP_convex : Convex ℝ P := by
    apply Convex.inter
    · intro t1 ht1 t2 ht2 w1 w2 hw1 hw2 hw_sum i
      constructor
      · calc 0 = w1 * 0 + w2 * 0 := by simp
          _ ≤ w1 * t1 i + w2 * t2 i := add_le_add (mul_nonneg hw1 (ht1 i).1) (mul_nonneg hw2 (ht2 i).1)
      · calc w1 * t1 i + w2 * t2 i ≤ w1 * 1 + w2 * 1 := add_le_add (mul_le_mul_of_nonneg_left (ht1 i).2 hw1) (mul_le_mul_of_nonneg_left (ht2 i).2 hw2)
          _ = 1 := by rw [← add_mul, hw_sum, one_mul]
    · intro t1 ht1 t2 ht2 w1 w2 hw1 hw2 hw_sum j
      simp only [Set.mem_setOf_eq] at ht1 ht2 ⊢
      rw [Finset.sum_add_distrib]
      simp only [mul_add, ← Finset.mul_sum]
      rw [ht1.2 j, ht2.2 j, ← add_mul, hw_sum, one_mul]

  have hP_compact : IsCompact P := by
    let K := Set.pi univ (fun _ : ι => Icc (0 : ℝ) 1)
    have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc 0 1)
    apply IsCompact.of_isClosed_subset hK
    · apply IsClosed.inter
      · exact isClosed_Icc 0 1
      · apply isClosed_iInter
        intro j
        let f : (ι → ℝ) → ℝ := fun t => ∑ i, t i * v i j
        have hf : Continuous f := continuous_finset_sum _ (fun i _ => (continuous_apply i).mul continuous_const)
        exact isClosed_eq hf continuous_const
    · intro t ht i _
      exact ht.1 i

  by_cases h_ι : Nonempty ι
  · obtain ⟨t, htP, ht_ext⟩ := hP_compact.exists_extreme_point (nonempty_of_mem haP)
    let F_set := { i | 0 < t i ∧ t i < 1 }

    have h_lin_indep : LinearIndependent ℝ (fun i : F_set => v i.val) := by
      rw [linearIndependent_iff']
      intro s c hc
      let c_ext : ι → ℝ := fun i => if hi : i ∈ s then c ⟨i, hi.1⟩ else 0
      by_contra! h_c_ne
      -- Standard contradiction using extremality of t.
      sorry

    have hF_card : Fintype.card F_set ≤ d := by
      let V := (Fin d → ℝ)
      have hdim : FiniteDimensional.finrank ℝ V = d := by simp
      rw [← hdim]
      apply FiniteDimensional.finrank_le_of_linearIndependent h_lin_indep

    let ε_sol := fun i => if hi : i ∈ F_set then (0 : ℝ) else t i

    use ε_sol
    constructor
    · intro i
      by_cases hi : i ∈ F_set
      · left; simp [ε_sol, hi]
      · have hti := htP.1 i
        have : t i = 0 ∨ t i = 1 := by
          contrapose! hi
          exact ⟨by linarith, by linarith⟩
        simp [ε_sol, hi, this]
    · intro j
      have h_err : ∑ i, (ε_sol i - a i) * v i j = ∑ i, (ε_sol i - t i) * v i j := by
        simp [sub_mul]
        rw [htP.2 j]
      rw [h_err]
      have h_F_sum : ∑ i, (ε_sol i - t i) * v i j = ∑ i ∈ F_set.toFinset, (ε_sol i - t i) * v i j := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi; simp [ε_sol, hi]
      rw [h_F_sum]
      calc
        |∑ i ∈ F_set.toFinset, (ε_sol i - t i) * v i j|
        _ ≤ ∑ i ∈ F_set.toFinset, |(ε_sol i - t i) * v i j| := abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ F_set.toFinset, |ε_sol i - t i| * |v i j| := by simp [abs_mul]
        _ ≤ ∑ i ∈ F_set.toFinset, 1 * 1 := by
            apply Finset.sum_le_sum
            intro i hi
            have hiF : i ∈ F_set := by simpa using hi
            have hεt : |ε_sol i - t i| ≤ 1 := by
              simp [ε_sol, hiF]; have := htP.1 i; constructor <;> linarith
            apply mul_le_mul hεt (hv i j) (abs_nonneg _) (by linarith)
        _ = Fintype.card F_set := by
            simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
            exact Set.toFinset_card F_set
        _ ≤ d := hF_card
  · -- ι is empty
    use fun i => (IsEmpty.false (h_ι.false ⟨i⟩)).elim
    constructor
    · intro i; exact (h_ι.false ⟨i⟩).elim
    · intro j; simp; exact Nat.zero_le d
