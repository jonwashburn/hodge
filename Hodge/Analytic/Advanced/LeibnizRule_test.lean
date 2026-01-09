import Hodge.Analytic.Advanced.LeibnizRule

open Manifold Set Filter
open scoped BigOperators

namespace LeibnizRule

variable {n k l : ℕ}

theorem alternatizeUncurryFin_wedge_right_test {k l : ℕ}
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
  -- Goal: ∑ i, (-1)^i • (A(v i) ∧ B) (removeNth i v) = ((alternatizeUncurryFin A) ∧ B) (v ∘ finCongr)
  -- Expand wedge on both sides
  simp only [ContinuousAlternatingMap.wedge_apply, ContinuousAlternatingMap.wedgeAlternating, ContinuousAlternatingMap.wedgeAlternatingTensor]
  -- This expands to domCoprod.summand
  admit

end LeibnizRule
