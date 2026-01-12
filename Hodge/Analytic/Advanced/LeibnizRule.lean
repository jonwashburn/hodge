/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Hodge.Analytic.Advanced.ContMDiffForms
import Hodge.Analytic.DomCoprod
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.GroupTheory.Perm.Fin

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

/-! ### Finite permutation bookkeeping

We will need explicit control over the sign of the “block swap” permutation on `Fin (k + l)` that
moves the last `l` coordinates in front of the first `k` coordinates.

Concretely, this permutation is a `k`-step rotation, so its sign is \((-1)^{k\cdot l}\).
-/

private lemma sign_finRotate' (N : ℕ) : Equiv.Perm.sign (finRotate N) = (-1 : ℤˣ) ^ (N - 1) := by
  cases N with
  | zero =>
    -- `finRotate 0 = 1`
    simp [finRotate]
  | succ n =>
    -- `finRotate (n+1)` has sign `(-1)^n`
    simpa [Nat.succ_sub_one] using (sign_finRotate n)

private lemma sign_finRotate_pow (N k : ℕ) :
    Equiv.Perm.sign ((finRotate N) ^ k) = (Equiv.Perm.sign (finRotate N)) ^ k := by
  -- `Equiv.Perm.sign` is a monoid hom, so it preserves powers
  simpa using map_pow (Equiv.Perm.sign) (finRotate N) k

/-- The `k`-step rotation on `Fin (k+l)` has sign `(-1)^(k*l)`. -/
private lemma sign_blockSwap (k l : ℕ) :
    Equiv.Perm.sign ((finRotate (k + l)) ^ k) = (-1 : ℤˣ) ^ (k * l) := by
  -- Compute sign via `sign_finRotate` and the fact that `k*(k-1)` is even.
  have h1 :
      Equiv.Perm.sign ((finRotate (k + l)) ^ k) =
        (Equiv.Perm.sign (finRotate (k + l))) ^ k := by
    simpa using sign_finRotate_pow (N := k + l) (k := k)
  -- Reduce to a pure `(-1)`-power identity in `ℤˣ`.
  rw [h1, sign_finRotate']
  -- Turn `(((-1)^(N-1))^k)` into `(-1)^((N-1)*k)`.
  rw [← pow_mul]
  cases k with
  | zero =>
    simp
  | succ k' =>
    -- Simplify the exponents `k+l-1` and `k*l` for `k = k'+1`.
    simp [Nat.succ_add]  -- turns `k'+1 + l - 1` into `k' + l` and `k*l` into `(k'+1)*l`
    -- Goal is now: `(-1) ^ ((k' + l) * (k' + 1)) = (-1) ^ ((k' + 1) * l)`.
    -- Rewrite `(k'+l)*(k'+1)` as `(k'+1)*l + (k'+1)*k'`, then kill the even term.
    have hk : (k' + l) * (k' + 1) = (k' + 1) * l + (k' + 1) * k' := by
      calc
        (k' + l) * (k' + 1) = (k' + 1) * (k' + l) := by simpa [Nat.mul_comm]
        _ = (k' + 1) * k' + (k' + 1) * l := by simp [Nat.mul_add]
        _ = (k' + 1) * l + (k' + 1) * k' := by ac_rfl
    rw [hk, pow_add]
    have hEven : Even ((k' + 1) * k') := Nat.even_mul_pred_self (k' + 1)
    rcases hEven with ⟨t, ht⟩
    have hkill : ((-1 : ℤˣ) ^ ((k' + 1) * k')) = 1 := by
      -- rewrite exponent as `2 * t`
      rw [ht, (two_mul t).symm, pow_mul]
      simp
    -- Cancel the extra factor.
    have hkill' : ((-1 : ℤˣ) ^ (k' * (k' + 1))) = 1 := by
      simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hkill
    simp [hkill', mul_assoc, mul_left_comm, mul_comm]

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

/-! #### Helper lemmas for wedge product distribution -/

/-- Wedge with zero on the left gives zero. -/
private lemma wedge_zero_left' {k l : ℕ} (B : Alt n l) : (0 : Alt n k).wedge B = 0 := by
  ext v
  simp only [ContinuousAlternatingMap.wedge_apply]
  unfold ContinuousAlternatingMap.wedgeAlternating ContinuousAlternatingMap.wedgeAlternatingTensor
  simp only [ContinuousAlternatingMap.toAlternatingMap_zero, TensorProduct.zero_tmul]
  simp

/-- Wedge distributes over finite sums in the left argument. -/
private lemma wedge_sum_left {k l : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Alt n k) (B : Alt n l) (s : Finset ι) :
    (∑ i ∈ s, f i).wedge B = ∑ i ∈ s, (f i).wedge B := by
  induction s using Finset.induction_on with
  | empty => simp [wedge_zero_left']
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [ContinuousAlternatingMap.wedge_add_left]
    rw [ih]

/-- Wedge distributes over finite sums (Fintype version). -/
private lemma wedge_finsum_left {k l : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Alt n k) (B : Alt n l) :
    (∑ i, f i).wedge B = ∑ i, (f i).wedge B := by
  convert wedge_sum_left f B Finset.univ <;> simp

/-- Wedge is compatible with integer scalar multiplication on the left. -/
private lemma wedge_zsmul_left {k l : ℕ} (c : ℤ) (ω : Alt n k) (B : Alt n l) :
    (c • ω).wedge B = c • (ω.wedge B) := by
  rw [← Int.cast_smul_eq_zsmul ℂ c ω]
  rw [← Int.cast_smul_eq_zsmul ℂ c (ω.wedge B)]
  exact ContinuousAlternatingMap.wedge_smul_left _ _ _

/-- Wedge distributes over finite sums with integer scalars. -/
private lemma wedge_zsmul_finsum_left {k l : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℤ) (f : ι → Alt n k) (B : Alt n l) :
    (∑ i, c i • f i).wedge B = ∑ i, c i • (f i).wedge B := by
  rw [wedge_finsum_left]
  congr 1
  ext i
  rw [wedge_zsmul_left]

/-! #### Base cases for shuffle bijection lemmas -/

/-- Base case for shuffle bijection right: when l = 0, B is a 0-form (scalar).
The wedge with a 0-form is just scalar multiplication, making the identity simple. -/
private lemma shuffle_bijection_right_l0 {k : ℕ}
    (v : Fin (k + 1) → TangentModel n)
    (A : TangentModel n →L[ℂ] Alt n k)
    (B : Alt n 0) :
    ∑ i : Fin (k + 1), ((-1 : ℤ)^(i : ℕ)) • ((A (v i)).wedge B) (Fin.removeNth i v) =
    ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).wedge B)
      (v ∘ finCongr (show (k+1)+0 = k+1 by omega)) := by
  -- When l = 0, B is a 0-form (scalar), so wedge with B is scalar multiplication
  -- B = constOfIsEmpty (B 0) where 0 : Fin 0 → E is the empty function
  have hB : B = ContinuousAlternatingMap.constOfIsEmpty ℂ (TangentModel n) (ι := Fin 0) (B (fun _ => 0)) := by
    ext u
    simp only [ContinuousAlternatingMap.constOfIsEmpty_apply]
    congr 1
    funext i
    exact i.elim0
  -- Rewrite B as constOfIsEmpty
  rw [hB]
  -- Use wedge_constOfIsEmpty_right: ω.wedge (const c) = c • ω.domDomCongr
  simp only [ContinuousAlternatingMap.wedge_constOfIsEmpty_right]
  simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.domDomCongr_apply]
  -- Both sides now have the scalar B(0) factored out
  -- LHS: ∑ i, (-1)^i • (B(0) • A(v i))(removeNth i v ∘ finCongr)
  -- RHS: B(0) • (alternatizeUncurryFin A)(v ∘ finCongr ∘ finCongr)
  --
  -- Use commutativity of scalar multiplication
  conv_lhs =>
    arg 2
    ext i
    rw [smul_comm]
  rw [← Finset.smul_sum]
  congr 1
  -- Now need: ∑ i, (-1)^i • A(v i)(removeNth i v ∘ finCongr) = (alternatizeUncurryFin A)(v ∘ finCongr ∘ finCongr)
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  -- Simplify finCongr ∘ finCongr
  simp only [Function.comp_apply, finCongr_apply, Fin.cast_eq_self]
  -- The sums should now match after simplifying finCongr
  -- Goal: ∑ i, (-1)^i • A(v i)(removeNth i v ∘ finCongr) = ∑ j, (-1)^j • A(v j)(removeNth j v)
  -- These are equal because finCongr is the identity when k+0 = k
  rfl

/-- Shuffle Bijection Lemma (right case): alternatization commutes with wedge when
the right factor is constant. This is the identity d(ω ∧ η) = dω ∧ η for constant η.

**Mathematical Statement**: When B is a constant l-form (independent of the tangent
direction), the alternatization of the wedge equals the wedge of the alternatization.
This encodes the product rule for exterior derivatives with a constant factor.

**Proof outline**:
- LHS: ∑_i (-1)^i • (A(v_i) ∧ B)(removeNth i v)  (derivative sum outer, shuffle inner)
- RHS: ((∑_j (-1)^j • A) ∧ B)(v)  (shuffle sum outer, derivative sum via alternatize)
- Both compute the same double sum after swapping (Fubini for finite sums)

**Base case l=0**: Proved in `shuffle_bijection_right_l0` using `wedge_constOfIsEmpty_right`

**TODO**: The general case (l > 0) requires constructing the explicit bijection between:
- Pairs (i, σ) on LHS: i ∈ Fin(k+l+1), σ is a (k,l)-shuffle
- Index structure on RHS: (k+1,l)-shuffles with alternatization encoding

Reference: Bott-Tu GTM 82, Warner GTM 94 Proposition 2.14. -/
private lemma shuffle_bijection_right {k l : ℕ}
    (v : Fin ((k+l)+1) → TangentModel n)
    (A : TangentModel n →L[ℂ] Alt n k)
    (B : Alt n l) :
    ∑ i : Fin ((k+l)+1), ((-1 : ℤ)^(i : ℕ)) • ((A (v i)).wedge B) (Fin.removeNth i v) =
    ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).wedge B)
      (v ∘ finCongr (show (k+1)+l = (k+l)+1 by omega)) := by
  -- Base case: when l = 0, B is a 0-form (scalar)
  cases l with
  | zero => exact shuffle_bijection_right_l0 v A B
  | succ l' =>
    -- General case (l > 0): Use linearity of wedge to expand the RHS.
    --
    -- Strategy:
    -- 1. RHS = (alternatizeUncurryFin A ∧ B)(v')
    --    where v' = v ∘ finCongr : Fin((k+1)+l') → TangentModel n
    -- 2. We want to show this equals the LHS sum.
    --
    -- The key is that both sides compute the exterior derivative d(A ∧ B)
    -- when viewed as a computation involving derivative indices and shuffles.
    --
    -- Both sides are double sums (derivative index × shuffles) that compute
    -- the same value by Fubini for finite sums + sign matching.
    --
    -- Mathematical reference: Bott-Tu GTM 82, Warner GTM 94 Proposition 2.14.
    --
    -- TODO: The formal bijection between index sets requires:
    -- - Explicit construction of the bijection (i, σ) ↔ (τ, j)
    -- - Proof of sign matching: (-1)^i × sign(σ) = sign(τ) × (-1)^j
    -- - Application of Finset.sum_bij
    sorry

/-- Main theorem: alternatization commutes with wedge when right factor is constant. -/
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
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
             ContinuousAlternatingMap.domDomCongr_apply]
  -- Use the shuffle bijection lemma
  have h_wedge_right : ∀ w, wedge_right w = (A w).wedge B := fun _ => rfl
  simp only [h_wedge_right]
  exact shuffle_bijection_right v A B

/-- Shuffle Bijection Lemma (left case): alternatization commutes with wedge when
the left factor is constant, with sign (-1)^k. This is d(ω ∧ η) = (-1)^k ω ∧ dη for constant ω.

**Mathematical Statement**: The sign (-1)^k accounts for moving the derivative index past
the k indices of the constant k-form A. This is the standard sign in graded commutativity.

**Index structure**:
- LHS: ∑_{i : Fin(k+l+1)} ∑_{σ : Shuffles(k,l)} (-1)^i × sign(σ) × (...)
- RHS: (-1)^k × ∑_{τ : Shuffles(k,l+1)} ∑_{j : Fin(l+1)} sign(τ) × (-1)^j × (...)

**Bijection**: (i, σ) ↔ (τ, j) with sign matching:
  (-1)^i × sign(σ) = (-1)^k × sign(τ) × (-1)^j

**Reference**: Bott-Tu GTM 82, Warner GTM 94 Proposition 2.14. -/
private lemma shuffle_bijection_left {k l : ℕ}
    (v : Fin ((k+l)+1) → TangentModel n)
    (A : Alt n k)
    (B : TangentModel n →L[ℂ] Alt n l) :
    ∑ i : Fin ((k+l)+1), ((-1 : ℤ)^(i : ℕ)) • (A.wedge (B (v i))) (Fin.removeNth i v) =
    ((-1 : ℂ)^k • A.wedge (ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) B))
      (v ∘ finCongr (show k+(l+1) = (k+l)+1 by omega)) := by
  -- This requires constructing an explicit signed bijection between the index sets.
  -- The formal proof would use Finset.sum_bij or similar infrastructure.
  -- Both sides compute the same double sum, organized differently, with signs matching.
  sorry

/-- Main theorem: alternatization commutes with wedge when left factor is constant. -/
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
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
             ContinuousAlternatingMap.domDomCongr_apply]
  -- Use the shuffle bijection lemma
  have h_wedge_left : ∀ w, wedge_left w = A.wedge (B w) := fun _ => rfl
  simp only [h_wedge_left]
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
