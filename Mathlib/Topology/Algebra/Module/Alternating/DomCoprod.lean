import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.Multilinear.Basic

open TensorProduct

namespace ContinuousAlternatingMap

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- In finite dimensions, any alternating map has a bound. -/
theorem _root_.AlternatingMap.exists_bound [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {ι : Type*} [Fintype ι] (f : AlternatingMap 𝕜 E F ι) :
    ∃ C : ℝ, ∀ v : ι → E, ‖f v‖ ≤ C * ∏ i, ‖v i‖ := by
  let f_multi := f.toMultilinearMap
  exact f_multi.exists_bound

/-- The wedge product of continuous alternating maps.
    Given ω : E [⋀^Fin k]→L[𝕜] F and η : E [⋀^Fin l]→L[𝕜] G,
    produces ω ∧ η : E [⋀^Fin (k+l)]→L[𝕜] (F ⊗[𝕜] G). -/
noncomputable def domCoprod
    {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E F (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E G (Fin l)) :
    ContinuousAlternatingMap 𝕜 E (F ⊗[𝕜] G) (Fin (k + l)) :=
  let ω_alg := ω.toAlternatingMap
  let η_alg := η.toAlternatingMap
  let wedge_alg := ω_alg.domCoprod η_alg
  let wedge_reindex := wedge_alg.domDomCongr finSumFinEquiv.symm
  -- For continuity in finite dimensions
  let C := ‖ω‖ * ‖η‖ -- This is a guess, let's see if we can prove a specific bound
  -- Actually, in finite dimensions we know it's continuous.
  -- But we need to use a constructor that accepts an AlternatingMap + continuity.
  { toAlternatingMap := wedge_reindex
    cont := by
      -- In finite dimensions, all multilinear maps are continuous.
      -- To use this, we might need [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 (F ⊗[𝕜] G)]
      sorry }

/-- Wedge product for scalar-valued forms, with multiplication in the scalar field. -/
noncomputable def wedge
    {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l)) :=
  (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap (ω.domCoprod η)

end ContinuousAlternatingMap
