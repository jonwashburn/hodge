/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Hodge.Analytic.Advanced.ContMDiffForms
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
open scoped BigOperators

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

/-- The manifold derivative of a wedge product follows the Leibniz rule (pointwise).

**Proof strategy**: For `modelWithCornersSelf`, `mfderiv` reduces to `fderiv` in chart coordinates.
The bilinear chain rule for wedge (`hasFDerivAt_wedge`) then gives the Leibniz formula.

The technical details involve:
1. Expressing mfderiv as fderivWithin on range I = univ (hence fderiv)
2. Identifying extChartAt with chartAt for modelWithCornersSelf
3. Applying hasFDerivAt_wedge to the chart representations
4. Relating fderiv of chart representation back to mfderiv -/
theorem mfderiv_wedge_apply {k l : ℕ} (ω : ContMDiffForm n X k) (η : ContMDiffForm n X l) (x : X)
    (v : TangentSpace (𝓒_complex n) x) :
    mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n (k+l)) (ω.wedge η).as_alternating x v =
    (mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n k) ω.as_alternating x v).wedge (η.as_alternating x) +
    (ω.as_alternating x).wedge (mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n l) η.as_alternating x v) := by
  -- The wedge of ContMDiffForms has as_alternating = fun x => ω(x) ∧ η(x)
  have h_eq : (ω.wedge η).as_alternating = fun y => (ω.as_alternating y).wedge (η.as_alternating y) := rfl
  rw [h_eq]

  -- Step 1: Get differentiability hypotheses
  have hω_diff : MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, Alt n k) ω.as_alternating x :=
    ω.smooth'.mdifferentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
  have hη_diff : MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, Alt n l) η.as_alternating x :=
    η.smooth'.mdifferentiableAt (by simp : (⊤ : WithTop ℕ∞) ≠ 0)

  -- Step 2: Define the bilinear wedge map on the product
  let B : Alt n k × Alt n l → Alt n (k + l) := fun p => p.1.wedge p.2
  have hB : IsBoundedBilinearMap ℂ B := isBoundedBilinearMap_wedge (n := n) (k := k) (l := l)

  -- Step 3: The pair function
  let pair : X → Alt n k × Alt n l := fun y => (ω.as_alternating y, η.as_alternating y)

  -- Step 4: Show the pair is differentiable
  have hpair_diff : MDifferentiableAt (𝓒_complex n) 𝓘(ℂ, Alt n k × Alt n l) pair x :=
    hω_diff.prodMk_space hη_diff

  -- Step 5: B is smooth (ContDiff)
  have hB_contDiff : ContDiff ℂ ⊤ B := hB.contDiff
  have hB_diff : DifferentiableAt ℂ B (pair x) :=
    hB_contDiff.differentiable (by simp : (⊤ : WithTop ℕ∞) ≠ 0) (pair x)

  -- Step 6: The function is B ∘ pair
  have h_comp : (fun y => (ω.as_alternating y).wedge (η.as_alternating y)) = B ∘ pair := rfl

  -- Step 7: Apply the chain rule for mfderiv
  rw [h_comp]
  rw [mfderiv_comp x hB_diff.mdifferentiableAt hpair_diff]

  -- Step 8: Simplify mfderiv of B using mfderiv_eq_fderiv (source is vector space)
  have h_mfderiv_B : mfderiv 𝓘(ℂ, Alt n k × Alt n l) 𝓘(ℂ, Alt n (k + l)) B (pair x) =
      fderiv ℂ B (pair x) := mfderiv_eq_fderiv

  -- Step 9: Get fderiv of bilinear map
  have h_fderiv_B : fderiv ℂ B (pair x) = hB.deriv (pair x) := hB.hasFDerivAt (pair x) |>.fderiv

  -- Step 10: Simplify mfderiv of pair using mfderiv_prodMk
  -- Use modelWithCornersSelf_prod and chartedSpaceSelf_prod to unify types
  have h_mfderiv_pair : mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n k × Alt n l) pair x =
      (mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n k) ω.as_alternating x).prod
        (mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n l) η.as_alternating x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact mfderiv_prodMk hω_diff hη_diff

  -- Step 11: Compute the final form
  simp only [h_mfderiv_B, h_fderiv_B, h_mfderiv_pair, IsBoundedBilinearMap.deriv, pair]
  show (hB.toContinuousLinearMap.deriv₂ (ω.as_alternating x, η.as_alternating x))
       ((mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n k) ω.as_alternating x v,
         mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n l) η.as_alternating x v)) =
       (mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n k) ω.as_alternating x v).wedge (η.as_alternating x) +
       (ω.as_alternating x).wedge (mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n l) η.as_alternating x v)
  -- Apply coe_deriv₂
  simp only [ContinuousLinearMap.coe_deriv₂]
  -- Goal: f (ω x) (mfderiv η v) + f (mfderiv ω v) (η x) = (mfderiv ω v).wedge (η x) + (ω x).wedge (mfderiv η v)
  -- These are equal by add_comm
  exact add_comm _ _

/-! ### Alternatization and Wedge Compatibility -/

/-- Alternatization commutes with wedge when the right argument is fixed.

The equality requires a cast since `(k+1)+l ≠ (k+l)+1` definitionally.

**Proof idea**: Both sides are sums over permutations (shuffles and alternatization indices).
The identity follows from the fact that the set of shuffles of `(k+1, l)` partitioned by the
position of the "derivative index" is in bijection with the shuffles of `(k, l)`.
-/
theorem alternatizeUncurryFin_wedge_right {k l : ℕ}
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
  -- 1. Expand definitions
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
             ContinuousAlternatingMap.domDomCongr_apply,
             wedge_right]
  -- 2. LHS: ∑ i, (-1)^i • (A(v i) ∧ B) (removeNth i v)
  --    RHS: ((alt A) ∧ B) (v ∘ finCongr)
  -- The identity is a combinatorial fact about shuffles.
  sorry

/-- Alternatization commutes with wedge when the left argument is fixed (with sign).

The sign (-1)^k arises from permuting the new index past k existing indices.
The equality requires a cast since `k+(l+1) ≠ (k+l)+1` definitionally.
-/
theorem alternatizeUncurryFin_wedge_left {k l : ℕ}
    (A : Alt n k) (B : TangentModel n →L[ℂ] Alt n l) :
    let wedge_left : TangentModel n →L[ℂ] Alt n (k + l) :=
      (ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l A) ∘L B
    ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) wedge_left =
    ContinuousAlternatingMap.domDomCongr
      ((-1 : ℂ)^k • A.wedge (ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) B))
      (finCongr (show k+(l+1) = (k+l)+1 by omega)) := by
  classical
  intro wedge_left
  ext v
  -- 1. Expand definitions
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
             ContinuousAlternatingMap.domDomCongr_apply,
             wedge_left]
  -- 2. The sign (-1)^k comes from the fact that alternatizeUncurryFin inserts
  -- the derivative index at position 0, which must be moved past k indices of A.
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
  classical
  -- 1. Unfold extDerivAt and wedge definition
  simp only [ContMDiffForm.extDerivAt, ContMDiffForm.wedge]

  -- 2. Define the components
  let A_ω := mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n k) ω.as_alternating x
  let B_η := η.as_alternating x
  let A_η := mfderiv (𝓒_complex n) 𝓘(ℂ, FiberAlt n l) η.as_alternating x
  let B_ω := ω.as_alternating x

  -- 3. Use mfderiv_wedge_apply
  -- At this point, the goal's LHS has the form alternatizeUncurryFin (mfderiv ... (fun y => ω y ∧ η y) x)
  -- mfderiv_wedge_apply ω η x provides exactly this derivative
  have hmf : mfderiv (𝓒_complex n) 𝓘(ℂ, Alt n (k+l)) (fun y => (ω.as_alternating y).wedge (η.as_alternating y)) x =
      (ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l).flip B_η ∘L A_ω +
      (ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l B_ω) ∘L A_η := by
    ext v
    simp only [ContinuousAlternatingMap.wedgeCLM_alt]
    exact mfderiv_wedge_apply ω η x v

  rw [hmf]

  -- 4. Use linearity of alternatizeUncurryFin
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_add]

  -- 5. Apply the two combinatorial lemmas
  rw [alternatizeUncurryFin_wedge_right A_ω B_η]
  rw [alternatizeUncurryFin_wedge_left B_ω A_η]

  -- 6. Normalize casts and signs
  simp only [castAlt]
  rfl

end LeibnizRule
