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
    · exact convex_Icc 0 1
    · intro t1 ht1 t2 ht2 w1 w2 hw1 hw2 hw_sum
      simp only [Set.mem_setOf_eq] at ht1 ht2 ⊢
      intro j
      rw [Finset.sum_add_distrib]
      simp only [mul_add, ← Finset.mul_sum]
      rw [ht1.2 j, ht2.2 j, ← add_mul, hw_sum, one_mul]
      
  have hP_compact : IsCompact P := by
    -- P is a closed subset of the compact set [0,1]^ι
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

  obtain ⟨t, htP, ht_ext⟩ := hP_compact.exists_extreme_point (nonempty_of_mem haP)
  
  let F_set := { i | 0 < t i ∧ t i < 1 }
  
  have h_lin_indep : LinearIndependent ℝ (fun i : F_set => v i.val) := by
    rw [linearIndependent_iff']
    intro s c hc
    let c_ext : ι → ℝ := fun i => if hi : i ∈ s then c ⟨i, hi.1⟩ else 0
    by_contra! h_c_ne
    
    -- If there's a linear dependency among fractional coordinates, 
    -- we can move in both directions and stay in P.
    have h_c_ext_sum : ∀ j, ∑ i, c_ext i * v i j = 0 := by
      intro j
      rw [Finset.sum_subset (Finset.subset_univ s)]
      · exact hc j
      · intro i _ hi; simp [c_ext, hi]

    -- Find small ε > 0 such that t ± ε c_ext ∈ [0,1]^ι.
    -- This is possible since 0 < t i < 1 for all i where c_ext i != 0.
    obtain ⟨ε, hε_pos, hε_bound⟩ : ∃ ε > 0, ∀ i, 0 ≤ t i + ε * c_ext i ∧ t i + ε * c_ext i ≤ 1 ∧
                                               0 ≤ t i - ε * c_ext i ∧ t i - ε * c_ext i ≤ 1 := by
      -- ι is finite, so we take the minimum room.
      sorry

    let t_plus := t + ε • c_ext
    let t_minus := t - ε • c_ext
    
    have ht_plus : t_plus ∈ P := by
      constructor
      · intro i; exact ⟨(hε_bound i).1, (hε_bound i).2.1⟩
      · intro j; simp [t_plus, add_mul, Finset.sum_add_distrib, htP.2 j, h_c_ext_sum j]
        
    have ht_minus : t_minus ∈ P := by
      constructor
      · intro i; exact ⟨(hε_bound i).2.2.1, (hε_bound i).2.2.2⟩
      · intro j; simp [t_minus, sub_mul, Finset.sum_sub_distrib, htP.2 j, h_c_ext_sum j]

    have h_mid : t = (1/2 : ℝ) • t_plus + (1/2 : ℝ) • t_minus := by
      ext i; simp [t_plus, t_minus]; ring
      
    have h_eq : t_plus = t_minus := ht_ext ht_plus ht_minus (by linarith) (by linarith) h_mid
    
    have h_c_zero : c_ext = 0 := by
      ext i
      have : t i + ε * c_ext i = t i - ε * c_ext i := congr_fun h_eq i
      linarith [hε_pos]
      
    apply h_c_ne
    ext ⟨i, hi⟩
    exact congr_fun h_c_zero i

  have hF_card : Fintype.card F_set ≤ d := by
    let V := (Fin d → ℝ)
    have hdim : FiniteDimensional.finrank ℝ V = d := by simp
    rw [← hdim]
    apply FiniteDimensional.finrank_le_of_linearIndependent h_lin_indep
    
  let ε := fun i => if hi : i ∈ F_set then (0 : ℝ) else t i
  
  use ε
  constructor
  · intro i
    by_cases hi : i ∈ F_set
    · left; simp [ε, hi]
    · have hti := htP.1 i
      have : t i = 0 ∨ t i = 1 := by
        contrapose! hi
        exact ⟨by linarith, by linarith⟩
      simp [ε, hi, this]
  · intro j
    have h_err : ∑ i, (ε i - a i) * v i j = ∑ i, (ε i - t i) * v i j := by
      simp [sub_mul]
      rw [htP.2 j]
    rw [h_err]
    have h_F_sum : ∑ i, (ε i - t i) * v i j = ∑ i ∈ F_set.toFinset, (ε i - t i) * v i j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi; simp [ε, hi]
    rw [h_F_sum]
    calc
      |∑ i ∈ F_set.toFinset, (ε i - t i) * v i j|
      _ ≤ ∑ i ∈ F_set.toFinset, |(ε i - t i) * v i j| := abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ F_set.toFinset, |ε i - t i| * |v i j| := by simp [abs_mul]
      _ ≤ ∑ i ∈ F_set.toFinset, 1 * 1 := by
          apply Finset.sum_le_sum
          intro i hi
          have hiF : i ∈ F_set := by simpa using hi
          have hεt : |ε i - t i| ≤ 1 := by
            simp [ε, hiF]; have := htP.1 i; constructor <;> linarith
          apply mul_le_mul hεt (hv i j) (abs_nonneg _) (by linarith)
      _ = Fintype.card F_set := by 
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact Set.toFinset_card F_set
      _ ≤ d := hF_card
