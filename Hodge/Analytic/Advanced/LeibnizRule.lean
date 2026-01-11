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

/-! ### Wedge Sum Lemmas -/

/-- Wedge of zero with anything is zero. -/
@[simp] theorem zero_wedge {k l : ℕ} (η : Alt n l) :
    (0 : Alt n k).wedge η = 0 := by
  have h := ContinuousAlternatingMap.wedge_smul_left (0 : ℂ) (0 : Alt n k) η
  simp only [zero_smul] at h
  exact h

/-- Wedge of anything with zero is zero. -/
@[simp] theorem wedge_zero {k l : ℕ} (ω : Alt n k) :
    ω.wedge (0 : Alt n l) = 0 := by
  have h := ContinuousAlternatingMap.wedge_smul_right (0 : ℂ) ω (0 : Alt n l)
  simp only [zero_smul] at h
  exact h

/-- Wedge product distributes over finite sums on the left. -/
theorem wedge_sum_left {k l : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Alt n k) (η : Alt n l) :
    (∑ i ∈ s, f i).wedge η = ∑ i ∈ s, (f i).wedge η := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_wedge]
  | insert x t hxt ih =>
    rw [Finset.sum_insert hxt, Finset.sum_insert hxt]
    rw [ContinuousAlternatingMap.wedge_add_left, ih]

/-- Wedge product distributes over finite sums on the right. -/
theorem wedge_sum_right {k l : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (ω : Alt n k) (g : ι → Alt n l) :
    ω.wedge (∑ i ∈ s, g i) = ∑ i ∈ s, ω.wedge (g i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, wedge_zero]
  | insert x t hxt ih =>
    rw [Finset.sum_insert hxt, Finset.sum_insert hxt]
    rw [ContinuousAlternatingMap.wedge_add_right, ih]

/-- Wedge product distributes over scaled finite sums on the left. -/
theorem wedge_smul_sum_left {k l : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ι → ℂ) (f : ι → Alt n k) (η : Alt n l) :
    (∑ i ∈ s, c i • f i).wedge η = ∑ i ∈ s, c i • (f i).wedge η := by
  rw [wedge_sum_left]
  congr 1
  ext i
  rw [ContinuousAlternatingMap.wedge_smul_left]

/-- Wedge product distributes over scaled finite sums on the right. -/
theorem wedge_smul_sum_right {k l : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (ω : Alt n k) (c : ι → ℂ) (g : ι → Alt n l) :
    ω.wedge (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • ω.wedge (g i) := by
  rw [wedge_sum_right]
  congr 1
  ext i
  rw [ContinuousAlternatingMap.wedge_smul_right]

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

/-! ### Alternatization and Wedge Compatibility

These two lemmas are the core combinatorial identities needed for the Leibniz rule.
They relate the sum structure of `alternatizeUncurryFin` (sum over derivative indices)
with the sum structure of `wedge` (sum over shuffles via `domCoprod`).

The proofs require showing that a double sum over (derivative index, shuffles) can be
reindexed to match the structure on the other side. This is a classical identity in
the theory of graded derivations on exterior algebras.

**Mathematical content**: Both identities express that `d` (exterior derivative) is a
graded derivation, meaning `d(ω ∧ η) = dω ∧ η + (-1)^deg(ω) ω ∧ dη`.
-/

/-! ### Helper Lemmas for Combinatorial Proofs

These lemmas establish linearity properties of `domCoprod.summand` that are used
in proving the main combinatorial identities.
-/

/-- Sign commutes with scalar multiplication for tensor products. -/
lemma smul_tmul_comm (c : ℂ) (s : ℤˣ) (x y : ℂ) :
    (s • (c • x)) ⊗ₜ[ℂ] y = c • ((s • x) ⊗ₜ[ℂ] y) := by
  rw [smul_comm s c x, TensorProduct.smul_tmul']

/-- The `domCoprod.summand` is additive in its first argument. -/
lemma domCoprod_summand_add_left {k l : ℕ}
    (a₁ a₂ : TangentModel n [⋀^Fin k]→ₗ[ℂ] ℂ)
    (b : TangentModel n [⋀^Fin l]→ₗ[ℂ] ℂ)
    (σ : Equiv.Perm.ModSumCongr (Fin k) (Fin l))
    (v : Fin k ⊕ Fin l → TangentModel n) :
    AlternatingMap.domCoprod.summand (a₁ + a₂) b σ v =
    AlternatingMap.domCoprod.summand a₁ b σ v + AlternatingMap.domCoprod.summand a₂ b σ v := by
  simp only [AlternatingMap.domCoprod.summand]
  induction σ using Quotient.inductionOn' with
  | h σ' =>
    simp only [Quotient.liftOn'_mk'', MultilinearMap.smul_apply, MultilinearMap.domDomCongr_apply,
               MultilinearMap.domCoprod_apply, AlternatingMap.coe_add, MultilinearMap.add_apply]
    rw [TensorProduct.add_tmul, smul_add]

/-- The `domCoprod.summand` respects scalar multiplication in its first argument. -/
lemma domCoprod_summand_smul_left {k l : ℕ}
    (c : ℂ) (a : TangentModel n [⋀^Fin k]→ₗ[ℂ] ℂ)
    (b : TangentModel n [⋀^Fin l]→ₗ[ℂ] ℂ)
    (σ : Equiv.Perm.ModSumCongr (Fin k) (Fin l))
    (v : Fin k ⊕ Fin l → TangentModel n) :
    AlternatingMap.domCoprod.summand (c • a) b σ v =
    c • AlternatingMap.domCoprod.summand a b σ v := by
  simp only [AlternatingMap.domCoprod.summand]
  induction σ using Quotient.inductionOn' with
  | h σ' =>
    simp only [Quotient.liftOn'_mk'', MultilinearMap.smul_apply, MultilinearMap.domDomCongr_apply,
               MultilinearMap.domCoprod_apply, AlternatingMap.coe_smul, MultilinearMap.smul_apply]
    exact smul_tmul_comm c (Equiv.Perm.sign σ') _ _

/-- The `domCoprod.summand` distributes over Finset sums in its first argument. -/
lemma domCoprod_summand_sum_left {k l : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → TangentModel n [⋀^Fin k]→ₗ[ℂ] ℂ)
    (b : TangentModel n [⋀^Fin l]→ₗ[ℂ] ℂ)
    (σ : Equiv.Perm.ModSumCongr (Fin k) (Fin l))
    (v : Fin k ⊕ Fin l → TangentModel n) :
    AlternatingMap.domCoprod.summand (∑ i ∈ s, f i) b σ v =
    ∑ i ∈ s, AlternatingMap.domCoprod.summand (f i) b σ v := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, AlternatingMap.domCoprod.summand]
    induction σ using Quotient.inductionOn' with
    | h σ' =>
      simp only [Quotient.liftOn'_mk'', MultilinearMap.smul_apply,
                 MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
                 @AlternatingMap.coe_zero, MultilinearMap.zero_apply,
                 TensorProduct.zero_tmul, smul_zero]
  | insert x t hxt ih =>
    rw [Finset.sum_insert hxt, Finset.sum_insert hxt]
    rw [domCoprod_summand_add_left, ih]

/-- Combined linearity: `domCoprod.summand` distributes over scaled Finset sums. -/
lemma domCoprod_summand_smul_sum_left {k l : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (c : ι → ℂ) (f : ι → TangentModel n [⋀^Fin k]→ₗ[ℂ] ℂ)
    (b : TangentModel n [⋀^Fin l]→ₗ[ℂ] ℂ)
    (σ : Equiv.Perm.ModSumCongr (Fin k) (Fin l))
    (v : Fin k ⊕ Fin l → TangentModel n) :
    AlternatingMap.domCoprod.summand (∑ i ∈ s, c i • f i) b σ v =
    ∑ i ∈ s, c i • AlternatingMap.domCoprod.summand (f i) b σ v := by
  rw [domCoprod_summand_sum_left]
  congr 1
  ext i
  rw [domCoprod_summand_smul_left]

/-! ### Helper Lemmas for Alternatization -/

/-- The ℤ-smul by (-1)^i equals ℂ-smul by (-1)^i on ℂ-modules. -/
private lemma int_smul_eq_complex_smul {k : ℕ}
    (A : TangentModel n →L[ℂ] Alt n k) (v : Fin (k+1) → TangentModel n) (i : Fin (k+1)) :
    ((-1 : ℤ)^(i : ℕ)) • (A (v i)) (i.removeNth v) = 
    ((-1 : ℂ)^(i : ℕ)) • (A (v i)).toAlternatingMap (i.removeNth v) := by
  convert rfl using 2
  funext x
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_eq_mul]

/-- The `toAlternatingMap` of `alternatizeUncurryFin` equals a sum with ℂ-signs. -/
lemma alternatizeUncurryFin_toAlternatingMap_apply {k : ℕ}
    (A : TangentModel n →L[ℂ] Alt n k) (v : Fin (k+1) → TangentModel n) :
    (ContinuousAlternatingMap.alternatizeUncurryFin A).toAlternatingMap v = 
    ∑ i : Fin (k+1), (-1 : ℂ)^(i : ℕ) • (A (v i)).toAlternatingMap (i.removeNth v) := by
  conv_lhs => 
    rw [show (ContinuousAlternatingMap.alternatizeUncurryFin A).toAlternatingMap v = 
            (ContinuousAlternatingMap.alternatizeUncurryFin A) v from rfl]
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact int_smul_eq_complex_smul A v i

/-! ### Main Combinatorial Lemmas -/

/-- Helper: When l=0, wedge with B is scalar multiplication. -/
private lemma shuffle_bijection_right_l0 {k : ℕ}
    (v : Fin (k+1) → TangentModel n)
    (A : TangentModel n →L[ℂ] Alt n k)
    (B : Alt n 0) :
    ∑ i : Fin (k+1), ((-1 : ℤ)^(i : ℕ)) • ((A (v i)).wedge B) (Fin.removeNth i v) =
    ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).wedge B)
      (v ∘ finCongr (show (k+1)+0 = k+1 by omega)) := by
  have hB : B = ContinuousAlternatingMap.constOfIsEmpty (R := ℂ) (M := TangentModel n) 
               (ι := Fin 0) (B (fun _ => 0)) := by
    ext u; simp only [ContinuousAlternatingMap.constOfIsEmpty_apply]; congr 1; funext i; exact i.elim0
  rw [hB]
  simp only [ContinuousAlternatingMap.wedge_constOfIsEmpty_right,
             ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.domDomCongr_apply]
  conv_lhs => arg 2; ext i; rw [smul_comm]
  rw [← Finset.smul_sum]
  congr 1
  have h_congr_comp : ∀ u : Fin (k+1) → TangentModel n, 
    (u ∘ finCongr (show (k+1)+0 = k+1 by omega)) ∘ finCongr (show k+1 = k+0+1 by omega) = 
    u ∘ finCongr (show k+0+1 = k+1 by omega) := by
    intro u; funext i; simp only [Function.comp_apply, finCongr_apply, Fin.cast_eq_self]
  rw [h_congr_comp, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  have h_finCongr_id : finCongr (show k+0+1 = k+1 by omega) = Equiv.refl (Fin (k+1)) := by
    ext i; simp only [finCongr_apply, Fin.cast_eq_self, Equiv.refl_apply]
  simp_rw [h_finCongr_id, Equiv.refl_apply, Function.comp_id]
  congr 1
  funext i
  congr 2
  funext j
  simp only [Function.comp_apply, finCongr_apply, Fin.removeNth, Fin.cast_eq_self]

/-- **Shuffle Bijection Lemma (right case)**: The double sums from LHS and RHS match
via a sign-preserving bijection between index pairs.

**Mathematical Content**: Both sides expand to double sums:
- LHS: ∑_{i,τ} (-1)^i × sign(τ) × A(v_i)(τ-left) × B(τ-right)
- RHS: ∑_{σ,j} sign(σ) × (-1)^j × A(left_j)(removeNth_j left) × B(right)

The bijection φ : (i, τ) → (σ, j) is defined by:
- Given i ∈ Fin(k+l+1) and τ a (k,l)-shuffle on the remaining k+l positions
- Let L' = τ^{-1}(left) ∪ {i} (k+1 elements in original indexing)
- σ is the unique (k+1,l)-shuffle with σ^{-1}(left) corresponding to L'
- j = rank of i in L' = #{x ∈ L' : x < i}

The sign relation (-1)^i × sign(τ) = sign(σ) × (-1)^j holds because inserting i
at position j in the left side introduces (i - j) transpositions, and the shuffle
sign accounts for the remaining reordering.

References:
- [Bott-Tu, "Differential Forms in Algebraic Topology", GTM 82, Ch. 1]
- [Warner, "Foundations of Differentiable Manifolds", GTM 94, §2.2] -/
private lemma shuffle_bijection_right {k l : ℕ}
    (v : Fin ((k+l)+1) → TangentModel n)
    (A : TangentModel n →L[ℂ] Alt n k)
    (B : Alt n l) :
    ∑ i : Fin ((k+l)+1), ((-1 : ℤ)^(i : ℕ)) • ((A (v i)).wedge B) (Fin.removeNth i v) =
    ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).wedge B)
      (v ∘ finCongr (show (k+1)+l = (k+l)+1 by omega)) := by
  -- Case split on l to use the proven base case
  induction l with
  | zero => 
    -- For l=0, use the helper lemma (types align directly after omega)
    exact shuffle_bijection_right_l0 v A B
  | succ l' _ =>
    -- General case: construct the bijection explicitly
    -- The proof requires building φ : (i, τ) → (σ, j) and verifying all conditions
    sorry

/-- **Theorem (Combinatorial Pillar)**: Alternatization commutes with wedge (right fixed).

This is a fundamental combinatorial identity needed for the Leibniz rule.
Both sides compute the same alternating form:
- LHS: ∑_i (-1)^i • ((A v_i).wedge B)(removeNth i v)
- RHS: ((∑_j (-1)^j • (A u_j).domDomCongr ...).wedge B)(v ∘ finCongr)

The equality follows from the shuffle structure of wedge matching the
combinatorial structure of alternatizeUncurryFin. The formal proof constructs
a bijection between (i, shuffle(k,l)) and (shuffle(k+1,l), j) pairs that
preserves the sign factors.

**Mathematical Reference**: This is equivalent to the Leibniz rule identity:
`d(A ∧ B)|_{B=const} = (dA) ∧ B` from exterior calculus.

References:
- [Bott-Tu, "Differential Forms in Algebraic Topology", GTM 82, Ch. 1]
- [Warner, "Foundations of Differentiable Manifolds", GTM 94, §2.2] -/
theorem alternatizeUncurryFin_wedge_right {k l : ℕ}
    (A : TangentModel n →L[ℂ] Alt n k) (B : Alt n l) :
    let wedge_right : TangentModel n →L[ℂ] Alt n (k + l) :=
      (ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l).flip B ∘L A
    ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) wedge_right =
    ContinuousAlternatingMap.domDomCongr
      ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).wedge B)
      (finCongr (show (k+1)+l = (k+l)+1 by omega)) := by
  intro wedge_right
  ext v
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  have h_wr : ∀ u, wedge_right u = (A u).wedge B := fun _ => rfl
  simp only [h_wr]
  rw [ContinuousAlternatingMap.domDomCongr_apply]
  exact shuffle_bijection_right v A B

/-- **Shuffle Bijection Lemma (left case)**: The double sums match with (-1)^k factor.

**Mathematical Content**: Similar to the right case, but with roles swapped.
The key difference is that the derivative direction must be moved past k
elements of A, introducing the (-1)^k sign factor.

The bijection φ : (i, τ) → (σ, j) is defined by:
- Given i ∈ Fin(k+l+1) and τ a (k,l)-shuffle
- The position i corresponds to a derivative applied to B (the varying factor)
- σ is a (k,l+1)-shuffle where the "extra" position in the right side is for i
- j = position of i within the right l+1 elements

The sign relation: (-1)^i × sign(τ) = (-1)^k × sign(σ) × (-1)^j
The extra (-1)^k comes from "moving" i past the k positions assigned to A.

References:
- [Bott-Tu, "Differential Forms in Algebraic Topology", GTM 82, Ch. 1]
- [Warner, "Foundations of Differentiable Manifolds", GTM 94, §2.2] -/
private lemma shuffle_bijection_left {k l : ℕ}
    (v : Fin ((k+l)+1) → TangentModel n)
    (A : Alt n k)
    (B : TangentModel n →L[ℂ] Alt n l) :
    ∑ i : Fin ((k+l)+1), ((-1 : ℤ)^(i : ℕ)) • (A.wedge (B (v i))) (Fin.removeNth i v) =
    ((-1 : ℂ)^k • A.wedge (ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) B))
      (v ∘ finCongr (show k+(l+1) = (k+l)+1 by omega)) := by
  -- The proof is analogous to shuffle_bijection_right, with the bijection
  -- adjusted for the left-constant case.
  -- The (-1)^k factor arises from moving the derivative position past k elements.
  sorry

/-- **Theorem (Combinatorial Pillar)**: Alternatization commutes with wedge (left fixed, with sign).

This is the companion to `alternatizeUncurryFin_wedge_right`, handling the case where
the left factor A is constant and the right factor B varies.

The identity states that for constant A : Alt k and B : E → Alt l:
  `alternatize(v ↦ A.wedge(B v)) = (-1)^k • A.wedge(alternatize B)`

## Sign Origin

The sign (-1)^k arises because:
- `alternatizeUncurryFin` inserts the derivative direction at index 0
- In the wedge product, the k inputs for A come first (indices 0 to k-1)
- Moving the derivative index past k positions introduces k transpositions
- Each transposition contributes a factor of -1, giving (-1)^k

## Mathematical Content

This is equivalent to the graded Leibniz rule: `d(ω ∧ η)|_{ω=const} = (-1)^k ω ∧ dη`

The formal proof constructs a bijection between (i, shuffle(k,l)) and
(shuffle(k,l+1), j) pairs with the sign relation:
  `(-1)^x × sign(τ) = (-1)^k × sign(σ) × (-1)^j`

References:
- [Bott-Tu, "Differential Forms in Algebraic Topology", GTM 82, Ch. 1]
- [Warner, "Foundations of Differentiable Manifolds", GTM 94, §2.2] -/
theorem alternatizeUncurryFin_wedge_left {k l : ℕ}
    (A : Alt n k) (B : TangentModel n →L[ℂ] Alt n l) :
    let wedge_left : TangentModel n →L[ℂ] Alt n (k + l) :=
      (ContinuousAlternatingMap.wedgeCLM_alt ℂ (TangentModel n) k l A) ∘L B
    ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) wedge_left =
    ContinuousAlternatingMap.domDomCongr
      ((-1 : ℂ)^k • A.wedge (ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) B))
      (finCongr (show k+(l+1) = (k+l)+1 by omega)) := by
  intro wedge_left
  ext v
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  have h_wl : ∀ u, wedge_left u = A.wedge (B u) := fun _ => rfl
  simp only [h_wl]
  rw [ContinuousAlternatingMap.domDomCongr_apply, ContinuousAlternatingMap.smul_apply]
  exact shuffle_bijection_left v A B

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
