import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Logic.Equiv.Fin.Basic

open TensorProduct

namespace ContinuousAlternatingMap

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

-- We need a topological space structure on the tensor product for the continuous alternating map.
-- For the general case, we might need a specific tensor product topology.
-- However, for the Hodge project, we often work in finite dimensions where the topology is unique.
variable [TopologicalSpace (F ⊗[𝕜] G)] [AddCommMonoid (F ⊗[𝕜] G)] [Module 𝕜 (F ⊗[𝕜] G)]
variable [ContinuousAdd (F ⊗[𝕜] G)] [ContinuousSMul 𝕜 (F ⊗[𝕜] G)]

/-- The wedge product of continuous alternating maps.
    Given ω : E [⋀^Fin k]→L[𝕜] F and η : E [⋀^Fin l]→L[𝕜] G,
    produces ω ∧ η : E [⋀^Fin (k+l)]→L[𝕜] (F ⊗[𝕜] G). -/
noncomputable def domCoprod 
    {k l : ℕ} 
    (ω : ContinuousAlternatingMap 𝕜 E F (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E G (Fin l)) :
    ContinuousAlternatingMap 𝕜 E (F ⊗[𝕜] G) (Fin (k + l)) :=
  { ω.toAlternatingMap.domCoprod η.toAlternatingMap |>.domDomCongr finSumFinEquiv.symm with
    cont := by
      -- The algebraic domCoprod is a finite sum of terms like
      -- sign σ • (ω.toMultilinearMap.domCoprod η.toMultilinearMap).domDomCongr σ
      -- Each term is continuous if ω and η are continuous multilinear maps.
      -- However, Mathlib's ContinuousMultilinearMap.domCoprod is not yet in Basic.
      -- In finite dimensions, continuity is automatic.
      apply continuous_of_linear_finiteDimensional
      -- This needs [FiniteDimensional 𝕜 E] and [FiniteDimensional 𝕜 (F ⊗[𝕜] G)]
      sorry }

/-- Wedge product for scalar-valued forms, with multiplication in the scalar field. -/
noncomputable def wedge
    {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E 𝕜 (Fin l)) :
    ContinuousAlternatingMap 𝕜 E 𝕜 (Fin (k + l)) :=
  -- Composition with the continuous linear map multiplication 𝕜 ⊗ 𝕜 → 𝕜
  -- Note: TensorProduct.lift (LinearMap.mul' 𝕜 𝕜) is the algebraic map.
  -- For 𝕜 = ℝ or ℂ, it is continuous.
  let mul_clm : (𝕜 ⊗[𝕜] 𝕜) →L[𝕜] 𝕜 := sorry -- isomorphism 𝕜 ⊗ 𝕜 ≃ 𝕜
  mul_clm.compContinuousAlternatingMap (ω.domCoprod η)

end ContinuousAlternatingMap
