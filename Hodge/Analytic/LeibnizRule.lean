/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Hodge.Analytic.ContMDiffForms
import Hodge.Analytic.DomCoprod
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Leibniz Rule for Exterior Derivative

This file provides the infrastructure to prove the graded Leibniz rule:
  d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη

## Main results

* `hasFDerivAt_wedge`: Derivative of wedge product of functions
* `mfderiv_wedge_apply`: Manifold derivative of wedge product
* `alternatizeUncurryFin_wedge_right`: Alternatization commutes with wedge (right fixed)
* `alternatizeUncurryFin_wedge_left`: Alternatization commutes with wedge (left fixed, with sign)
* `extDerivAt_wedge`: Exterior derivative of wedge product (the Leibniz rule)

## Implementation notes

The graded sign (-1)^k arises from the fact that `alternatizeUncurryFin` inserts the
derivative direction at the first index, while the wedge product naturally combines
indices from both forms. Moving the derivative index past k indices of a k-form
introduces the sign.
-/

open Manifold Set Filter

variable {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

namespace LeibnizRule

/-- Helper abbreviation for the fiber alternating maps. -/
abbrev Alt (n k : ℕ) := ContinuousAlternatingMap ℂ (TangentModel n) ℂ (Fin k)

/-! ### Derivative of Wedge Product -/

/-- The wedge product is a bounded bilinear map.
This is the key ingredient for computing derivatives of wedge products. -/
lemma isBoundedBilinearMap_wedge {k l : ℕ} :
    IsBoundedBilinearMap ℂ (fun p : Alt n k × Alt n l => p.1.wedge p.2) where
  add_left := fun x₁ x₂ y => ContinuousAlternatingMap.wedge_add_left x₁ x₂ y
  smul_left := fun c x y => ContinuousAlternatingMap.wedge_smul_left c x y
  add_right := fun x y₁ y₂ => ContinuousAlternatingMap.wedge_add_right x y₁ y₂
  smul_right := fun c x y => ContinuousAlternatingMap.wedge_smul_right c x y
  bound := by
    -- The wedge is the composition of wedgeCLM_alt with function application
    -- wedgeCLM_alt : Alt k →L[ℂ] (Alt l →L[ℂ] Alt (k+l))
    -- So (ω, η) ↦ (wedgeCLM_alt ω) η is bounded bilinear
    let f := ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l
    -- Use that (g, x) ↦ g x for g : E →L F, x : E is bounded bilinear
    -- with bound max ‖f‖ 1
    have h := f.isBoundedBilinearMap
    obtain ⟨C, hC_pos, hC⟩ := h.bound
    exact ⟨C, hC_pos, hC⟩

/-- The derivative of the wedge product of two form-valued functions.

If `ω : G → Alt n k` and `η : G → Alt n l` are differentiable at x, then
`y ↦ ω(y) ∧ η(y)` is differentiable and its derivative is:
  `v ↦ (Dω(v)) ∧ η(x) + ω(x) ∧ (Dη(v))`
-/
theorem hasFDerivAt_wedge {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {k l : ℕ} {ω : G → Alt n k} {η : G → Alt n l} {x : G}
    {ω' : G →L[ℂ] Alt n k} {η' : G →L[ℂ] Alt n l}
    (hω : HasFDerivAt ω ω' x) (hη : HasFDerivAt η η' x) :
    HasFDerivAt (fun y => (ω y).wedge (η y))
      (isBoundedBilinearMap_wedge.deriv (ω x, η x) ∘L (ω'.prod η')) x := by
  -- Use the bounded bilinear map derivative rule
  have hB := isBoundedBilinearMap_wedge (n := n) (k := k) (l := l)
  -- hB.hasFDerivAt gives: HasFDerivAt wedge (hB.deriv (a, b)) (a, b)
  -- where hB.deriv (a, b) (v₁, v₂) = a.wedge v₂ + v₁.wedge b
  have hBilin := hB.hasFDerivAt (ω x, η x)
  -- Compose with (ω, η) : G → Alt k × Alt l using the chain rule
  have hPair : HasFDerivAt (fun y => (ω y, η y)) (ω'.prod η') x := hω.prodMk hη
  exact hBilin.comp x hPair

/-- The manifold derivative of a wedge product follows the Leibniz rule (pointwise). -/
theorem mfderiv_wedge_apply {k l : ℕ} (ω : ContMDiffForm n X k) (η : ContMDiffForm n X l) (x : X)
    (v : TangentSpace (𝓒_complex n) x) :
    mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n (k+l)) (ω.wedge η).as_alternating x v =
    (mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n k) ω.as_alternating x v).wedge (η.as_alternating x) +
    (ω.as_alternating x).wedge (mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n l) η.as_alternating x v) := by
  -- The wedge of ContMDiffForms has as_alternating = fun x => ω(x) ∧ η(x)
  have h_eq : (ω.wedge η).as_alternating = fun y => (ω.as_alternating y).wedge (η.as_alternating y) := rfl
  rw [h_eq]

  -- For smooth forms, we use that mfderiv can be computed via chart coordinates.
  -- Key facts:
  -- 1. For modelWithCornersSelf: range I = univ, so mfderiv = fderivWithin ... univ = fderiv (in chart)
  -- 2. For 𝓘(ℂ, F) target: writtenInExtChartAt is essentially f ∘ (chartAt x).symm
  -- 3. The bilinear derivative rule (hasFDerivAt_wedge) applies in chart coordinates

  -- Smoothness gives differentiability
  have hω_diff : MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, Alt n k) ω.as_alternating x :=
    ω.smooth'.mdifferentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
  have hη_diff : MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, Alt n l) η.as_alternating x :=
    η.smooth'.mdifferentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
  have hωη_diff : MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, Alt n (k+l))
      (fun y => (ω.as_alternating y).wedge (η.as_alternating y)) x :=
    (ω.wedge η).smooth'.mdifferentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)

  -- The proof uses the chain rule for mfderiv with a bilinear map.
  --
  -- Key structure:
  -- 1. wedge : Alt k × Alt l → Alt (k+l) is a smooth bilinear map
  -- 2. (ω, η) : X → Alt k × Alt l has mfderiv = (mfderiv ω, mfderiv η) by HasMFDerivAt.prodMk
  -- 3. wedge ∘ (ω, η) has mfderiv = D(wedge)((ω x, η x)) ∘ mfderiv (ω, η) by chain rule
  -- 4. For bilinear W: DW((a,b))(v₁,v₂) = W(v₁,b) + W(a,v₂)
  --
  -- Therefore:
  --   mfderiv (ω.wedge η) x v = (mfderiv ω x v).wedge (η x) + (ω x).wedge (mfderiv η x v)
  --
  -- The formal proof requires:
  -- (a) Showing wedge has HasMFDerivAt with derivative = isBoundedBilinearMap_wedge.deriv
  -- (b) Using HasMFDerivAt.comp with HasMFDerivAt.prodMk
  -- (c) Unfolding the derivative formula
  --
  -- For 𝓘(ℂ, F) targets (model spaces), this reduces to HasFDerivAt via
  -- hasMFDerivAt_iff_hasFDerivAt, and we can use hasFDerivAt_wedge directly.
  --
  -- Implementation path:
  -- 1. Get HasMFDerivAt for ω and η from smoothness
  -- 2. Use HasMFDerivAt.prodMk to get HasMFDerivAt for (ω, η)
  -- 3. wedge is a CLM^2 so it has HasMFDerivAt = bilinear deriv
  -- 4. Compose and evaluate at v
  sorry

/-! ### Alternatization and Wedge Compatibility -/

/-- Alternatization commutes with wedge when the right argument is fixed.

The equality requires a cast since `(k+1)+l ≠ (k+l)+1` definitionally.

**Proof idea**: By `alternatizeUncurryFin_apply`:
  `alternatizeUncurryFin (wedge_right) v = ∑ i, (-1)^i • (A(v i) ∧ B) (removeNth i v)`

Since wedge is linear in first arg:
  `(A(v i) ∧ B) (removeNth i v) = (A(v i) ∧ B) (u)`
  where `u = removeNth i v` is the remaining `(k+l)`-tuple.

The RHS wedge applies `(alternatizeUncurryFin A).wedge B` to a `(k+1)+l`-tuple.
By definition of wedge:
  `((alternatizeUncurryFin A).wedge B) w = (alternatizeUncurryFin A)(w ∘ castAdd l) ∧ B(w ∘ natAdd (k+1))`

The key is showing these agree up to the index reordering captured by `domDomCongr`.
-/
theorem alternatizeUncurryFin_wedge_right {k l : ℕ}
    (A : TangentModel n →L[ℂ] Alt n k) (B : Alt n l) :
    let wedge_right : TangentModel n →L[ℂ] Alt n (k + l) :=
      (ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l).flip B ∘L A
    ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) wedge_right =
    ContinuousAlternatingMap.domDomCongr
      ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).wedge B)
      (finCongr (show (k+1)+l = (k+l)+1 by omega)) := by
  -- Apply extensionality
  ext v
  -- Unfold alternatizeUncurryFin on LHS
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  -- The key is relating the sum over i to the wedge structure
  -- This requires careful analysis of how indices map through finCongr
  sorry

/-- Alternatization commutes with wedge when the left argument is fixed (with sign).

The sign (-1)^k arises from permuting the new index past k existing indices.
The equality requires a cast since `k+(l+1) ≠ (k+l)+1` definitionally.

**Proof idea**: By `alternatizeUncurryFin_apply`:
  `alternatizeUncurryFin (wedge_left) v = ∑ i, (-1)^i • (A ∧ B(v i)) (removeNth i v)`

The RHS applies `A.wedge (alternatizeUncurryFin B)` to a `k+(l+1)`-tuple.
By wedge definition:
  `(A.wedge (alternatizeUncurryFin B)) w = A(w ∘ castAdd (l+1)) ∧ (alternatizeUncurryFin B)(w ∘ natAdd k)`

The sign (-1)^k comes from moving the derivative index (which alternatizeUncurryFin inserts
at position 0) past the k indices of A. This is exactly the graded sign in the Leibniz rule.
-/
theorem alternatizeUncurryFin_wedge_left {k l : ℕ}
    (A : Alt n k) (B : TangentModel n →L[ℂ] Alt n l) :
    let wedge_left : TangentModel n →L[ℂ] Alt n (k + l) :=
      (ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l A) ∘L B
    ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) wedge_left =
    ContinuousAlternatingMap.domDomCongr
      ((-1 : ℂ)^k • A.wedge (ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) B))
      (finCongr (show k+(l+1) = (k+l)+1 by omega)) := by
  -- Apply extensionality
  ext v
  -- Unfold alternatizeUncurryFin on LHS
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  -- The sign (-1)^k arises from the permutation that moves index 0 past k indices
  -- This is the mathematical content of the graded Leibniz rule
  sorry

/-! ### The Leibniz Rule -/

/-- Cast a `ContinuousAlternatingMap` along an equality of the index cardinality. -/
noncomputable def castAlt {m m' : ℕ} (h : m = m') (f : Alt n m) : Alt n m' :=
  ContinuousAlternatingMap.domDomCongr f (finCongr h)

/-- **Leibniz rule for exterior derivative**: d(ω ∧ η) = dω ∧ η + (-1)^k ω ∧ dη.

This is the fundamental identity relating the exterior derivative to the wedge product.
It expresses that d is a graded derivation on the exterior algebra.
-/
theorem extDerivAt_wedge {k l : ℕ} (ω : ContMDiffForm n X k) (η : ContMDiffForm n X l) (x : X) :
    ContMDiffForm.extDerivAt (ω.wedge η) x =
    castAlt (show (k+1)+l = (k+l)+1 by omega)
      ((ContMDiffForm.extDerivAt ω x).wedge (η.as_alternating x)) +
    castAlt (show k+(l+1) = (k+l)+1 by omega)
      (((-1 : ℂ)^k) • (ω.as_alternating x).wedge (ContMDiffForm.extDerivAt η x)) := by
  -- The proof combines:
  -- 1. mfderiv_wedge_apply: bilinear derivative rule
  -- 2. alternatizeUncurryFin_add: additivity of alternatization
  -- 3. alternatizeUncurryFin_wedge_right and alternatizeUncurryFin_wedge_left
  -- 4. Type casts via castAlt
  sorry

end LeibnizRule
