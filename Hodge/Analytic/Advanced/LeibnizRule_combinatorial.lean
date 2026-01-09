import Hodge.Analytic.Advanced.LeibnizRule

open Manifold Set Filter
open scoped BigOperators

namespace LeibnizRule

variable {n k l : ℕ}

theorem alternatizeUncurryFin_wedge_right_real {k l : ℕ}
    (A : TangentModel n →L[ℂ] Alt n k) (B : Alt n l) :
    let wedge_right : TangentModel n →L[ℂ] Alt n (k + l) :=
      (ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l).flip B ∘L A
    ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) wedge_right =
    ContinuousAlternatingMap.domDomCongr
      ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).wedge B)
      (finCongr (show (k+1)+l = (k+l)+1 by omega)) := by
  classical
  intro wedge_right
  ext v
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply, ContinuousAlternatingMap.domDomCongr_apply, wedge_right]
  simp only [ContinuousAlternatingMap.wedge_apply, ContinuousAlternatingMap.wedgeAlternating,
             ContinuousAlternatingMap.wedgeAlternatingTensor]
  -- Now we have two sums over ModSumCongr
  -- LHS: ∑ i : Fin (k+l+1), (-1)^i • ∑ σ : ModSumCongr (Fin k) (Fin l), sign σ • (A(v i) ⊗ B) ((removeNth i v) ∘ σ)
  -- RHS: ∑ σ : ModSumCongr (Fin (k+1)) (Fin l), sign σ • (alternatizeUncurryFin A ⊗ B) ((v ∘ finCongr) ∘ σ)
  -- Expand alternatizeUncurryFin A on RHS
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  -- RHS: ∑ σ : ModSumCongr (Fin (k+1)) (Fin l), sign σ • ( (∑ j : Fin (k+1), (-1)^j • A(...) ) ⊗ B )
  admit

end LeibnizRule
