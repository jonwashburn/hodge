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

/-! ### A `cycleRange`-based decomposition of `Perm (Fin (n+1))`

`Equiv.Perm.decomposeFin` decomposes a permutation using a single transposition `swap 0 p`,
so its sign contribution is `-1` (for `p ≠ 0`). For Leibniz-type identities we need the finer
`(-1)^p` factor, which is exactly the sign of the cycle `(0 1 ... p)` i.e. `Fin.cycleRange p`.

We package the standard trick:

Given `σ : Perm (Fin (n+1))`, let `p := σ 0` and set `σ' := p.cycleRange * σ`.
Then `σ' 0 = 0`, so `σ'` is determined by its restriction to `Fin n` (via successors).
Conversely, given `(p, e)` with `e : Perm (Fin n)`, we reconstruct
`σ := p.cycleRange.symm * decomposeFin.symm (0, e)`.

This normalization yields the clean sign identity
`sign σ = (-1)^p * sign e`.
-/

private noncomputable def decomposeFinCycleRange_toFun {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    Fin (n + 1) × Equiv.Perm (Fin n) :=
  let p : Fin (n + 1) := σ 0
  let σ' : Equiv.Perm (Fin (n + 1)) := p.cycleRange * σ
  (p, (Equiv.Perm.decomposeFin σ').2)

private noncomputable def decomposeFinCycleRange_invFun {n : ℕ} (pe : Fin (n + 1) × Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  let p : Fin (n + 1) := pe.1
  let e : Equiv.Perm (Fin n) := pe.2
  p.cycleRange.symm * (Equiv.Perm.decomposeFin.symm (0, e))

private lemma decomposeFinCycleRange_left_inv {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    decomposeFinCycleRange_invFun (n := n) (decomposeFinCycleRange_toFun (n := n) σ) = σ := by
  classical
  -- Set up the normalization.
  set p : Fin (n + 1) := σ 0
  set σ' : Equiv.Perm (Fin (n + 1)) := p.cycleRange * σ
  have hσ'0 : σ' 0 = 0 := by
    simp [σ', p, Fin.cycleRange_self]
  -- Let `pe := decomposeFin σ'`. Since `σ' 0 = 0`, we have `pe.1 = 0`.
  set pe : Fin (n + 1) × Equiv.Perm (Fin n) := Equiv.Perm.decomposeFin σ' with hpe
  have hpe1 : pe.1 = 0 := by
    -- Turn `pe = decomposeFin σ'` into `decomposeFin.symm pe = σ'`.
    have hsymm : Equiv.Perm.decomposeFin.symm pe = σ' := by
      have := congrArg (Equiv.Perm.decomposeFin.symm) hpe
      -- RHS simplifies by `symm_apply_apply`.
      simpa using this
    have h0 := congrArg (fun τ => τ 0) hsymm
    -- Compute the LHS using `decomposeFin_symm_apply_zero` (after destructing `pe`).
    have hL : (Equiv.Perm.decomposeFin.symm pe) 0 = pe.1 := by
      rcases pe with ⟨p0, e0⟩
      simp [Equiv.Perm.decomposeFin_symm_apply_zero]
    -- Now `h0` becomes `pe.1 = σ' 0 = 0`.
    -- RHS is `σ' 0 = 0`.
    exact (hL.symm.trans h0).trans hσ'0
  have hpe0 : pe = (0, pe.2) := by
    ext <;> simp [hpe1]
  have hσ' : σ' = Equiv.Perm.decomposeFin.symm (0, pe.2) := by
    -- First show `decomposeFin σ' = (0, pe.2)`.
    have hdecomp : Equiv.Perm.decomposeFin σ' = (0, pe.2) := by
      -- `pe = decomposeFin σ'` by definition, and `pe = (0, pe.2)` from `hpe0`.
      exact hpe.symm.trans hpe0
    -- Apply `decomposeFin.symm` to both sides and simplify.
    have := congrArg (Equiv.Perm.decomposeFin.symm) hdecomp
    simpa using this
  -- Now cancel the normalization.
  -- invFun(toFun σ) = p.cycleRange.symm * σ' = σ.
  -- since `σ' = p.cycleRange * σ`.
  -- First rewrite `decomposeFin.symm (0, pe.2)` as `σ'`, then cancel.
  have hσ'symm : Equiv.Perm.decomposeFin.symm (0, pe.2) = σ' := hσ'.symm
  -- We avoid `simp` recursion by doing the cancellation explicitly.
  calc
    decomposeFinCycleRange_invFun (n := n) (decomposeFinCycleRange_toFun (n := n) σ)
        = p.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, pe.2) := by
            simp [decomposeFinCycleRange_toFun, decomposeFinCycleRange_invFun, p, σ', pe]
    _ = p.cycleRange.symm * σ' := by simpa [hσ'symm]
    _ = p.cycleRange.symm * (p.cycleRange * σ) := by simp [σ']
    _ = (p.cycleRange.symm * p.cycleRange) * σ := by
          simpa [mul_assoc] using (mul_assoc p.cycleRange.symm p.cycleRange σ).symm
    _ = σ := by simp

private lemma decomposeFinCycleRange_right_inv {n : ℕ} (pe : Fin (n + 1) × Equiv.Perm (Fin n)) :
    decomposeFinCycleRange_toFun (n := n) (decomposeFinCycleRange_invFun (n := n) pe) = pe := by
  classical
  rcases pe with ⟨p, e⟩
  -- Compute `toFun (invFun (p,e))`.
  ext
  · -- first component
    -- Unfold `toFun`: the first component is evaluation at `0`.
    simp [decomposeFinCycleRange_toFun, decomposeFinCycleRange_invFun, Equiv.Perm.mul_apply,
      Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]
  · -- second component
    -- The normalized permutation is exactly `decomposeFin.symm (0,e)`.
    have hnorm :
        p.cycleRange * (p.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, e)) =
          Equiv.Perm.decomposeFin.symm (0, e) := by
      -- cancel `p.cycleRange` with its inverse
      calc
        p.cycleRange * (p.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, e))
            = (p.cycleRange * p.cycleRange.symm) * Equiv.Perm.decomposeFin.symm (0, e) := by
              simpa [mul_assoc] using
                (mul_assoc p.cycleRange p.cycleRange.symm (Equiv.Perm.decomposeFin.symm (0, e))).symm
        _ = Equiv.Perm.decomposeFin.symm (0, e) := by simp
    -- Apply `decomposeFin` to both sides and take `Prod.snd`.
    have hdecomp :
        (Equiv.Perm.decomposeFin
            (p.cycleRange * (p.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, e)))).2 = e := by
      -- `decomposeFin (decomposeFin.symm (0,e)) = (0,e)`
      simpa [hnorm] using congrArg Prod.snd (Equiv.apply_symm_apply (Equiv.Perm.decomposeFin) (0, e))
    simpa [decomposeFinCycleRange_toFun, decomposeFinCycleRange_invFun, hdecomp]

private noncomputable def decomposeFinCycleRange {n : ℕ} :
    Equiv.Perm (Fin (n + 1)) ≃ Fin (n + 1) × Equiv.Perm (Fin n) :=
  ⟨decomposeFinCycleRange_toFun (n := n), decomposeFinCycleRange_invFun (n := n),
    decomposeFinCycleRange_left_inv (n := n), decomposeFinCycleRange_right_inv (n := n)⟩

private lemma decomposeFinCycleRange_symm_apply_zero {n : ℕ} (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    (decomposeFinCycleRange (n := n)).symm (p, e) 0 = p := by
  classical
  simp [decomposeFinCycleRange, decomposeFinCycleRange_invFun, Fin.cycleRange_symm_zero]

private lemma decomposeFinCycleRange_symm_apply_succ {n : ℕ} (p : Fin (n + 1)) (e : Equiv.Perm (Fin n))
    (x : Fin n) :
    (decomposeFinCycleRange (n := n)).symm (p, e) x.succ = p.succAbove (e x) := by
  classical
  -- Use `decomposeFin_symm_apply_succ` with `p = 0`, then `cycleRange_symm_succ`.
  simp [decomposeFinCycleRange, decomposeFinCycleRange_invFun,
    Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]

private lemma decomposeFinCycleRange_symm_sign {n : ℕ} (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign ((decomposeFinCycleRange (n := n)).symm (p, e)) =
      (-1 : ℤˣ) ^ (p : ℕ) * Equiv.Perm.sign e := by
  classical
  -- `sign` is a monoid hom; use `sign_mul`, `sign_inv`, `sign_cycleRange`,
  -- and `decomposeFin.symm_sign` at `p = 0`.
  simp [decomposeFinCycleRange, decomposeFinCycleRange_invFun,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign]

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

/-! #### Helper lemma: `domCoprod` as full alternatization

Mathlib relates the shuffle-based `AlternatingMap.domCoprod` to the “full alternatization” of the
underlying multilinear `MultilinearMap.domCoprod`.  This is sometimes a more convenient form for
sum-reindexing arguments, because it replaces the quotient over shuffles by a sum over *all*
permutations (at the cost of a factorial scaling). -/

private lemma domCoprod_smul_factorial_eq_alternatization {k l : ℕ}
    (ω : Alt n k) (η : Alt n l) :
    (k.factorial * l.factorial) • (ω.toAlternatingMap.domCoprod η.toAlternatingMap) =
      MultilinearMap.alternatization
        ((ω.toAlternatingMap.toMultilinearMap).domCoprod (η.toAlternatingMap.toMultilinearMap)) := by
  -- This is `MultilinearMap.domCoprod_alternization_eq`, specialized to `Fin k`, `Fin l`, and `ℂ`.
  -- We write it in the “scaled domCoprod = alternatization” direction.
  -- Note: the scalar here is an `ℕ`-scalar (`nsmul`), exactly matching Mathlib's statement.
  simpa using
    (MultilinearMap.domCoprod_alternization_eq (a := ω.toAlternatingMap) (b := η.toAlternatingMap)).symm

private lemma domCoprod_eq_inv_factorial_smul_alternatization {k l : ℕ}
    (ω : Alt n k) (η : Alt n l) :
    ω.toAlternatingMap.domCoprod η.toAlternatingMap =
      (((k.factorial * l.factorial : ℕ) : ℂ)⁻¹) •
        MultilinearMap.alternatization
          ((ω.toAlternatingMap.toMultilinearMap).domCoprod (η.toAlternatingMap.toMultilinearMap)) := by
  classical
  -- Start from the `nsmul` (Nat-scalar) identity, then convert it to an `ℂ`-scalar identity and cancel.
  set m : ℕ := k.factorial * l.factorial
  have hNat :
      m • (ω.toAlternatingMap.domCoprod η.toAlternatingMap) =
        MultilinearMap.alternatization
          ((ω.toAlternatingMap.toMultilinearMap).domCoprod (η.toAlternatingMap.toMultilinearMap)) := by
    simpa [m] using
      (domCoprod_smul_factorial_eq_alternatization (n := n) (k := k) (l := l) ω η)
  have h :
      ((m : ℂ) • (ω.toAlternatingMap.domCoprod η.toAlternatingMap)) =
        MultilinearMap.alternatization
          ((ω.toAlternatingMap.toMultilinearMap).domCoprod (η.toAlternatingMap.toMultilinearMap)) := by
    -- Rewrite the Nat action as scalar multiplication by `(m : ℂ)`.
    -- `Nat.cast_smul_eq_nsmul` has the form `(↑m : ℂ) • x = m • x`.
    simpa [Nat.cast_smul_eq_nsmul] using hNat
  have hm : (m : ℂ) ≠ 0 := by
    -- `m = k! * l!` is a positive natural number.
    have hmNat : m ≠ 0 := by
      simp [m, Nat.mul_ne_zero, Nat.factorial_ne_zero]
    exact_mod_cast hmNat
  -- Multiply both sides by the inverse scalar and simplify.
  have h' := congrArg (fun z => ((m : ℂ)⁻¹) • z) h
  -- LHS simplifies by `inv_mul_cancel₀` + `smul_smul`.
  have hinv : (m : ℂ)⁻¹ * (m : ℂ) = 1 := inv_mul_cancel₀ hm
  -- Turn `((m⁻¹) • ((m) • x))` into `((m⁻¹*m) • x)` and cancel.
  simpa [smul_smul, hinv, one_smul] using h'

private lemma wedge_apply_eq_inv_factorial_smul_alternatization {k l : ℕ}
    (ω : Alt n k) (η : Alt n l) (v : Fin (k + l) → TangentModel n) :
    (ω.wedge η) v =
      (((k.factorial * l.factorial : ℕ) : ℂ)⁻¹) •
        (LinearMap.mul' ℂ ℂ)
          ((MultilinearMap.alternatization
              ((ω.toAlternatingMap.toMultilinearMap).domCoprod (η.toAlternatingMap.toMultilinearMap)))
            (v ∘ finSumFinEquiv)) := by
  classical
  -- Unfold the wedge definition down to `AlternatingMap.domCoprod`, then rewrite using the inverse-factorial lemma.
  simp only [ContinuousAlternatingMap.wedge_apply,
    ContinuousAlternatingMap.wedgeAlternating,
    ContinuousAlternatingMap.wedgeAlternatingTensor]
  simp only [AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod'_apply]
  -- Replace the shuffle-quotient `domCoprod` by the full alternatization sum.
  -- (We keep the result *before* expanding the alternatization sum.)
  rw [domCoprod_eq_inv_factorial_smul_alternatization (n := n) (k := k) (l := l) ω η]
  -- Pull the scalar out through the linear map `LinearMap.mul'`.
  simp [map_smul, smul_smul]

/-! #### Core reindexing lemma for the right-constant Leibniz identity

This is the combinatorial heart of `shuffle_bijection_right` for `l > 0`, written at the level of
the “full alternatization” sums over permutations.

It expresses that (after clearing factorial scalars) the alternatization sum for
`(alternatizeUncurryFin A) ∧ B` can be rewritten as a signed sum over the removed index `x`,
matching the definition of `alternatizeUncurryFin`.
-/
set_option maxHeartbeats 800000

private lemma stage1_lemma {k l : ℕ} {n : ℕ}
    (w : (Fin (k + 1) ⊕ Fin l) → TangentModel n)
    (A : TangentModel n →L[ℂ] Alt n k)
    (B : Alt n l) :
    (∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A)
                (fun i : Fin (k + 1) => w (σ (Sum.inl i))) *
              B (fun j : Fin l => w (σ (Sum.inr j))))) =
      (k + 1 : ℂ) *
        ∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            (A (w (σ (Sum.inl 0)))
                (fun i : Fin k => w (σ (Sum.inl i.succ))) *
              B (fun j : Fin l => w (σ (Sum.inr j)))) := by
  classical
  -- Helper abbreviations
  let left (σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l)) : Fin (k + 1) → TangentModel n :=
    fun i => w (σ (Sum.inl i))
  let right (σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l)) : Fin l → TangentModel n :=
    fun j => w (σ (Sum.inr j))

  -- Step 1: Expand alternatizeUncurryFin and distribute
  have hexpand : ∀ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A) (left σ) * B (right σ)) =
      ∑ i : Fin (k + 1),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((-1 : ℂ) ^ (i : ℕ)) *
          (A (left σ i) (i.removeNth (left σ)) * B (right σ)) := by
    intro σ
    rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    -- The apply gives: ∑ i, (-1)^i • A(left σ i)(removeNth i (left σ))
    -- Convert zsmul to ℂ multiplication
    have hzsmul : ∀ i : Fin (k + 1),
        ((-1 : ℤ) ^ (i : ℕ)) • A (left σ i) (i.removeNth (left σ)) =
        ((-1 : ℂ) ^ (i : ℕ)) * A (left σ i) (i.removeNth (left σ)) := by
      intro i
      rw [← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
      simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
    simp_rw [hzsmul]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

  -- Apply expansion
  conv_lhs =>
    arg 2
    ext σ
    rw [hexpand σ]
  -- Step 2: Swap order of summation
  rw [Finset.sum_comm]

  -- Step 3-4: Show each inner sum (over σ) is the same for all i
  have hinner : ∀ i : Fin (k + 1),
      ∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((-1 : ℂ) ^ (i : ℕ)) *
          (A (left σ i) (i.removeNth (left σ)) * B (right σ)) =
      ∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (A (left σ 0) ((0 : Fin (k + 1)).removeNth (left σ)) * B (right σ)) := by
    intro i
    -- Define τ_i := sumCongr (cycleRange i) 1 (NOT the inverse!)
    -- Then σ ↦ τ * σ maps: σ(inl 0) → τ(σ(inl 0)), with τ(inl j) = inl (cycleRange i j)
    -- cycleRange i maps: 0 → 1 → 2 → ... → i → 0 (cycle)
    -- So τ * σ applied to inl 0 gives σ(inl (cycleRange i 0)) = σ(inl 1) if i ≥ 1
    -- Actually we want: σ(inl 0) → σ(inl i)
    -- Use σ ↦ σ * τ with τ = sumCongr (cycleRange i)⁻¹ 1, then
    -- (σ * τ)(inl 0) = σ(τ(inl 0)) = σ(inl ((cycleRange i)⁻¹ 0)) = σ(inl i)
    -- because cycleRange⁻¹ sends 0 to i.
    let τ : Equiv.Perm (Fin (k + 1) ⊕ Fin l) := Equiv.Perm.sumCongr i.cycleRange.symm 1
    -- sign(τ) = sign(cycleRange⁻¹) = sign(cycleRange) = (-1)^i
    have hsignτ : Equiv.Perm.sign τ = (-1 : ℤˣ) ^ (i : ℕ) := by
      simp only [τ, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_one, mul_one]
      conv_lhs => rw [show i.cycleRange.symm = i.cycleRange⁻¹ from rfl, Equiv.Perm.sign_inv]
      exact Fin.sign_cycleRange i
    have hsignτ' : (Equiv.Perm.sign τ : ℤ) = (-1 : ℤ) ^ (i : ℕ) := by
      simp only [hsignτ, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    -- Fintype.sum_equiv e f g h shows: ∑_σ f(e σ) = ∑_σ g(σ) when h σ : f(e σ) = g σ
    -- We have:
    --   f(σ) = source = sign(σ) * (-1)^i * A(left σ i)...
    --   g(σ) = target = sign(σ) * A(left σ 0)...
    -- We want ∑ f = ∑ g, but sum_equiv gives ∑ f∘e = ∑ g
    -- Use symmetry: prove ∑ g = ∑ f, then apply symm
    -- For this, we need sum_equiv e' g f h' where g(e' σ) = f(σ)
    -- With e' = mulRight τ⁻¹, we get g(σ * τ⁻¹) = f(σ)
    -- i.e., sign(σ*τ⁻¹) * A(left(σ*τ⁻¹) 0)... = sign(σ) * (-1)^i * A(left σ i)...
    -- Using sign(τ⁻¹) = sign(τ) = (-1)^i and left(σ*τ⁻¹) 0 = σ(τ⁻¹(inl 0)) = σ(inl (cycleRange 0))
    -- cycleRange at 0 is cycleRange i applied to 0 gives... 1 (for i > 0) or 0 (for i = 0)
    -- This is getting complicated. Let me use the direct approach.
    -- 
    -- Direct approach: ∑ f = ∑ g by showing f(σ) = g(σ * τ) for the right τ
    -- f_i(σ) = sign(σ) * (-1)^i * A(left σ i)...
    -- g(σ') = sign(σ') * A(left σ' 0)...
    -- For σ' = σ * τ with τ = sumCongr cycleRange.symm 1:
    --   left σ' 0 = σ(τ(inl 0)) = σ(inl i) = left σ i
    --   sign(σ') = sign(σ) * (-1)^i
    -- So g(σ * τ) = sign(σ) * (-1)^i * A(left σ i)... = f_i(σ)
    -- Therefore ∑_σ f_i(σ) = ∑_σ g(σ * τ) = ∑_σ' g(σ') by bijection
    refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ ?_
    intro σ
    -- Goal: f(σ) = g((mulRight τ) σ) = g(σ * τ)
    -- f(σ) = sign(σ) * (-1)^i * A(left σ i)...
    -- g(σ * τ) = sign(σ * τ) * A(left(σ*τ) 0)...
    -- Properties:
    have hsignστ : (Equiv.Perm.sign (σ * τ) : ℤ) =
          (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (i : ℕ) := by
      simp only [Equiv.Perm.sign_mul, hsignτ', Units.val_mul]
    -- (σ * τ)(inl 0) = σ(τ(inl 0)) = σ(inl (cycleRange i)⁻¹ 0) = σ(inl i)
    have hleft_i : left (σ * τ) 0 = left σ i := by
      simp only [left, τ, Equiv.Perm.mul_apply, Equiv.Perm.sumCongr_apply, Sum.map_inl,
        Fin.cycleRange_symm_zero]
    -- For x : Fin k, (σ * τ)(inl (succAbove 0 x)) = σ(τ(inl x.succ))
    -- τ(inl x.succ) = inl ((cycleRange i)⁻¹ x.succ) = inl (succAbove i ((cycleRange i)⁻¹.predAbove 0 x))
    -- Actually (cycleRange i)⁻¹ x.succ = succAbove i x (this is the key property!)
    have hremove : (0 : Fin (k + 1)).removeNth (left (σ * τ)) = i.removeNth (left σ) := by
      ext x
      simp only [left, τ, Fin.removeNth, Equiv.Perm.mul_apply, Equiv.Perm.sumCongr_apply,
        Sum.map_inl, Fin.succAbove_zero, Fin.cycleRange_symm_succ]
    have hright : right (σ * τ) = right σ := by
      ext j
      simp only [right, τ, Equiv.Perm.mul_apply, Equiv.Perm.sumCongr_apply, Sum.map_inr,
        Equiv.Perm.one_apply]
    -- Now combine
    -- The goal is: f(σ) = g((mulRight τ) σ) = g(σ * τ)
    -- f(σ) = sign(σ) * (-1)^i * A(left σ i)...
    -- g(σ * τ) = sign(σ * τ) * A(left(σ*τ) 0)...
    -- Using: sign(σ * τ) = sign(σ) * (-1)^i, left(σ*τ) 0 = left σ i, etc.
    have hmr : (Equiv.mulRight τ) σ = σ * τ := rfl
    simp only [hmr]
    -- Expand sign(σ * τ)
    rw [hsignστ, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    -- Use the lemmas to show the terms match
    rw [hleft_i, hremove, hright]
    -- Goal is now reflexively true

  simp_rw [hinner]
  -- Step 5: The sum over i is (k+1) copies of the same thing
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  -- Convert ↑(k + 1) to (↑k + 1) and unfold `left`, `right`
  simp only [Nat.cast_add, Nat.cast_one, left, right]
  -- The remaining difference: Fin.removeNth 0 f vs fun i => f i.succ
  -- Use: removeNth 0 f = fun i => f (succAbove 0 i) = fun i => f i.succ
  have hremNth : ∀ (f : Fin (k + 1) → TangentModel n),
      (Fin.removeNth 0 f) = (fun i : Fin k => f i.succ) := by
    intro f
    ext i
    simp only [Fin.removeNth, Fin.succAbove_zero]
  simp_rw [hremNth]

private lemma stage2_lemma {k l : ℕ}
    (v : Fin (k + l + 1) → TangentModel n)
    (A : TangentModel n →L[ℂ] Alt n k)
    (B : Alt n l) :
    let h : (k + 1) + l = (k + l) + 1 := by omega
    let w : (Fin (k + 1) ⊕ Fin l) → TangentModel n := (v ∘ finCongr h) ∘ finSumFinEquiv
    (∑ σ : Equiv.Perm (Fin (k + 1) ⊕ Fin l),
          ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            (A (w (σ (Sum.inl 0)))
                (fun i : Fin k => w (σ (Sum.inl i.succ))) *
              B (fun j : Fin l => w (σ (Sum.inr j))))) =
    ∑ x : Fin (k + l + 1),
          ((-1 : ℂ) ^ (x : ℕ)) *
            (LinearMap.mul' ℂ ℂ)
              ((MultilinearMap.alternatization
                  ((A (v x)).toMultilinearMap.domCoprod B.toMultilinearMap))
                ((Fin.removeNth x v) ∘ finSumFinEquiv)) := by
  intro h w
  classical
  let equiv := (Equiv.permCongr ((finSumFinEquiv (m := k + 1) (n := l)).trans (finCongr h))).trans (decomposeFinCycleRange (n := k + l))
  
  let reindexed_term (p : Fin (k + l + 1) × Equiv.Perm (Fin (k + l))) : ℂ :=
    ((Equiv.Perm.sign (equiv.symm p) : ℤ) : ℂ) *
      (A (w (equiv.symm p (Sum.inl 0)))
          (fun i : Fin k => w (equiv.symm p (Sum.inl i.succ))) *
        B (fun j : Fin l => w (equiv.symm p (Sum.inr j))))

  trans ∑ p, reindexed_term p
  · refine Fintype.sum_equiv equiv _ _ ?_
    intro σ
    dsimp [reindexed_term]
    simp only [Equiv.symm_apply_apply]

  rw [Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ ?_
  intro x
  
  let M := ((A (v x)).toMultilinearMap.domCoprod B.toMultilinearMap)
  let u := (Fin.removeNth x v) ∘ finSumFinEquiv
  
  have hsign : ∀ e, ((Equiv.Perm.sign (equiv.symm (x, e)) : ℤ) : ℂ) = 
               ((-1 : ℂ) ^ (x : ℕ)) * ((Equiv.Perm.sign e : ℤ) : ℂ) := by
     intro e
     simp [equiv, decomposeFinCycleRange_symm_sign, Equiv.Perm.sign_permCongr, mul_comm]

  dsimp [reindexed_term]
  simp_rw [hsign]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  
  -- Expand RHS: (mul' ℂ ℂ) (alternatization M) u
  simp only [M, u, MultilinearMap.alternatization_apply, LinearMap.mul'_apply]
  
  -- Both sides are sums over e : Perm(Fin(k+l))
  -- LHS: ∑ e, sign(e) * A(w(equiv.symm(x,e)(inl 0)))... * B...
  -- RHS: (∑ e, sign(e) • M.domDomCongr e u).1 * (∑ e, sign(e) • M.domDomCongr e u).2
  -- Actually, mul' takes a tensor product and multiplies, so we need to be careful.
  
  -- The alternatization produces an AlternatingMap, and when evaluated it gives an element of the tensor.
  -- Then mul' ℂ ℂ : ℂ ⊗ ℂ → ℂ multiplies the components.
  
  -- For domCoprod M, the alternatization gives a sum over shuffles, and we need to match this
  -- with the LHS sum structure.
  
  -- The key insight is that both sides, when fully expanded, sum over the same permutation group
  -- with matching terms. The index correspondence via equiv.symm makes them equal.
  
  -- Due to the complexity of the tensor product expansion and the multi-layered equivalences,
  -- this requires careful term matching. The mathematical content is:
  -- - w ∘ equiv.symm(x,e) evaluated at (inl 0, inl i.succ, inr j) matches
  -- - (v x, u ∘ e) evaluated at (first arg, inl i, inr j)
  
  -- The key lemmas are:
  -- 1. w(equiv.symm(x,e)(inl 0)) = v x
  -- 2. w(equiv.symm(x,e)(inl i.succ)) = u(e(inl i')) for appropriate i'
  -- 3. w(equiv.symm(x,e)(inr j)) = u(e(inr j'))
  
  -- These follow from:
  -- - decomposeFinCycleRange_symm_apply_zero
  -- - decomposeFinCycleRange_symm_apply_succ
  -- - The structure of permCongr and the finSumFinEquiv bijection
  
  -- Reference: Warner GTM 94, Proposition 2.14; Federer GMT Ch 4
  sorry

private lemma alternatizeUncurryFin_domCoprod_alternatization_wedge_right_core {k l : ℕ}
    (v : Fin (k + l + 1) → TangentModel n)
    (A : TangentModel n →L[ℂ] Alt n k)
    (B : Alt n l) :
    (LinearMap.mul' ℂ ℂ)
        ((MultilinearMap.alternatization
            ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).toMultilinearMap.domCoprod
              B.toMultilinearMap))
          (((v ∘ finCongr (show (k + 1) + l = (k + l) + 1 by omega)) ∘ finSumFinEquiv))) =
      (k + 1 : ℂ) *
        ∑ x : Fin (k + l + 1),
          ((-1 : ℂ) ^ (x : ℕ)) *
            (LinearMap.mul' ℂ ℂ)
              ((MultilinearMap.alternatization
                  ((A (v x)).toMultilinearMap.domCoprod B.toMultilinearMap))
                ((Fin.removeNth x v) ∘ finSumFinEquiv)) := by
  classical
  let h : (k + 1) + l = (k + l) + 1 := by omega
  let v' : Fin ((k + 1) + l) → TangentModel n := v ∘ finCongr h
  let w : (Fin (k + 1) ⊕ Fin l) → TangentModel n := v' ∘ finSumFinEquiv

  -- The proof uses stage1_lemma and stage2_lemma:
  -- 1. Expand alternatization to sum over permutations
  -- 2. stage1_lemma extracts the (k+1) factor from alternatizeUncurryFin
  -- 3. stage2_lemma relates the permutation sum to the removeNth indexing
  --
  -- Note: This requires stage2_lemma which still has a sorry
  have hstage1 := stage1_lemma w A B
  have hstage2 := stage2_lemma v A B
  
  -- The LHS can be rewritten using alternatization expansion and domCoprod
  -- After expansion, use stage1_lemma to factor out (k+1)
  -- Then stage2_lemma gives the relation to the RHS
  
  -- This proof requires completing stage2_lemma first
  sorry

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
    classical
    -- General case (l = l' + 1 > 0).
    -- Rewrite the wedge terms using the full alternatization (sum over *all* permutations)
    -- to avoid working directly with the shuffle quotient `ModSumCongr`.
    have hw :
        ∀ i : Fin (k + (l' + 1) + 1),
          ((A (v i)).wedge B) (Fin.removeNth i v) =
            (((k.factorial * (l' + 1).factorial : ℕ) : ℂ)⁻¹) •
              (LinearMap.mul' ℂ ℂ)
                ((MultilinearMap.alternatization
                    (((A (v i)).toAlternatingMap.toMultilinearMap).domCoprod
                      (B.toAlternatingMap.toMultilinearMap)))
                  ((Fin.removeNth i v) ∘ finSumFinEquiv)) := by
      intro i
      simpa using
        (wedge_apply_eq_inv_factorial_smul_alternatization (n := n) (k := k) (l := l' + 1)
          (ω := A (v i)) (η := B) (v := Fin.removeNth i v))
    have hwR :
        ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).wedge B)
            (v ∘ finCongr (show (k + 1) + (l' + 1) = (k + (l' + 1)) + 1 by omega)) =
          ((((Nat.factorial (k + 1) * (l' + 1).factorial : ℕ) : ℂ)⁻¹)) •
            (LinearMap.mul' ℂ ℂ)
              ((MultilinearMap.alternatization
                  (((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).toAlternatingMap.toMultilinearMap).domCoprod
                    (B.toAlternatingMap.toMultilinearMap)))
                (((v ∘ finCongr (show (k + 1) + (l' + 1) = (k + (l' + 1)) + 1 by omega)) ∘ finSumFinEquiv))) := by
      -- direct application of the wedge rewrite lemma
      simpa using
        (wedge_apply_eq_inv_factorial_smul_alternatization (n := n) (k := k + 1) (l := l' + 1)
          (ω := ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A) (η := B)
          (v := (v ∘ finCongr (show (k + 1) + (l' + 1) = (k + (l' + 1)) + 1 by omega))))
    -- Rewrite both sides.
    simp only [hw, hwR]
    -- TODO (Agent 1): finish by expanding `alternatizeUncurryFin_apply` and reindexing the
    -- resulting finite sums over permutations (Fubini + `Finset.sum_bij`).
    -- Normalize the scalar weights and clear common factors.
    -- This reduces the statement to a pure alternatization reindexing identity.
    classical
    -- First, rewrite the two factorial inverses so both sides share `(l'+1)!⁻¹ * k!⁻¹`.
    have hkfac_inv :
        (↑((k + 1).factorial) : ℂ)⁻¹ = (k + 1 : ℂ)⁻¹ * (↑(k.factorial) : ℂ)⁻¹ := by
      have hk :
          (↑((k + 1).factorial) : ℂ) = (k + 1 : ℂ) * (↑(k.factorial) : ℂ) := by
        simpa [Nat.factorial_succ, Nat.cast_mul] using
          (congrArg (fun n : ℕ => (n : ℂ)) (Nat.factorial_succ k)).symm
      calc
        (↑((k + 1).factorial) : ℂ)⁻¹ = ((k + 1 : ℂ) * (↑(k.factorial) : ℂ))⁻¹ := by simpa [hk]
        _ = (↑(k.factorial) : ℂ)⁻¹ * (k + 1 : ℂ)⁻¹ := by simp [mul_inv_rev]
        _ = (k + 1 : ℂ)⁻¹ * (↑(k.factorial) : ℂ)⁻¹ := by ac_rfl

    -- Convert the goal to a form where we can cancel the nonzero common scalar.
    have hl0 : (↑((l' + 1).factorial) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (l' + 1)
    have hk0 : (↑(k.factorial) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have hk10 : (k + 1 : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero k
    let c : ℂ := (↑((l' + 1).factorial) : ℂ)⁻¹ * (↑(k.factorial) : ℂ)⁻¹
    have hc : c ≠ 0 := by
      refine mul_ne_zero (inv_ne_zero hl0) (inv_ne_zero hk0)
    -- Package the unscaled alternatization terms.
    let tL (x : Fin (k + (l' + 1) + 1)) : ℂ :=
      (LinearMap.mul' ℂ ℂ)
        ((MultilinearMap.alternatization
            ((A (v x)).toMultilinearMap.domCoprod B.toMultilinearMap))
          ((Fin.removeNth x v) ∘ finSumFinEquiv))
    let tR : ℂ :=
      (LinearMap.mul' ℂ ℂ)
        ((MultilinearMap.alternatization
            ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).toMultilinearMap.domCoprod
              B.toMultilinearMap))
          (((v ∘ finCongr (show (k + 1) + (l' + 1) = (k + (l' + 1)) + 1 by omega)) ∘ finSumFinEquiv)))

    -- Rewrite both factorial scalars into the common factor `c`.
    have hcL :
        ((↑(k.factorial * (l' + 1).factorial) : ℂ)⁻¹) = c := by
      simp [c, Nat.cast_mul, mul_inv_rev]
    have hcR :
        ((↑((k + 1).factorial * (l' + 1).factorial) : ℂ)⁻¹) = (k + 1 : ℂ)⁻¹ * c := by
      -- use `hkfac_inv` for `(k+1)!` and commutativity
      simp [c, hkfac_inv, Nat.cast_mul, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

    -- Fold the large alternatization expressions into `tL`/`tR` without unfolding them.
    have htL' :
        ∀ x : Fin (k + (l' + 1) + 1),
          (LinearMap.mul' ℂ ℂ)
              ((MultilinearMap.alternatization
                  ((A (v x)).toMultilinearMap.domCoprod B.toMultilinearMap))
                ((Fin.removeNth x v) ∘ finSumFinEquiv)) =
            tL x := by
      intro x; rfl
    have htR' :
        (LinearMap.mul' ℂ ℂ)
            ((MultilinearMap.alternatization
                ((ContinuousAlternatingMap.alternatizeUncurryFin (F := ℂ) A).toMultilinearMap.domCoprod
                  B.toMultilinearMap))
              (((v ∘ finCongr (show (k + 1) + (l' + 1) = (k + (l' + 1)) + 1 by omega)) ∘ finSumFinEquiv))) =
          tR := by
      rfl

    -- Rewrite the goal using the folded expressions and the common scalar `c`.
    -- We keep `simp` tightly controlled to avoid unfolding the alternatization sums.
    -- First, fold the big terms and rewrite the factorial scalars via `hcL`/`hcR`.
    -- Then convert the remaining `•`-actions in `ℂ` into multiplication.
    simp only [htL', htR']
    -- Rewrite the factorial inverse scalars.
    -- (They appear inside the rewritten wedge formulas from `hw`/`hwR`.)
    simp only [hcL, hcR]
    -- Finally, normalize `ℂ` scalar actions.
    simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

    -- Factor out the common scalar `c` from both sides, cancel it, and clear `(k+1)⁻¹`.
    have hL :
        (∑ x : Fin (k + (l' + 1) + 1), (-1) ^ (x : ℕ) * (c * tL x)) =
          c * (∑ x : Fin (k + (l' + 1) + 1), (-1) ^ (x : ℕ) * tL x) := by
      -- expand the RHS using `Finset.mul_sum` and rearrange each term
      classical
      simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        using (Finset.mul_sum (s := (Finset.univ : Finset (Fin (k + (l' + 1) + 1))))
          (f := fun x => (-1) ^ (x : ℕ) * tL x) c).symm

    have hR :
        (k + 1 : ℂ)⁻¹ * (c * tR) = c * ((k + 1 : ℂ)⁻¹ * tR) := by
      -- commutativity in `ℂ`
      ac_rfl

    -- Use `hL`/`hR` to rewrite the goal as `c * Σ = c * ((k+1)⁻¹ * tR)`.
    -- Then it suffices to prove `Σ = (k+1)⁻¹ * tR`, which follows from the core lemma.
    -- (The rewrite may be blocked if simp normalized exponents differently, so we do it by `simp`.)
    -- Rewrite both sides in place.
    -- LHS
    -- (Turn `(-1 : ℂ)^(x:ℕ)` into `(-1 : ℂ)^(x:ℤ)` if necessary, then apply `hL`.)
    -- RHS similarly.
    -- We use `rw` and `simp` to match the patterns exactly.
    -- First, rewrite to the exact `hL`/`hR` patterns.
    -- (No-op if already in that form.)
    -- Now apply the rewrites.
    rw [hL, hR]

    -- Core lemma gives `tR = (k+1) * Σ` (with the Nat-exponent form).
    have hreindexNat :
        tR =
          (k + 1 : ℂ) *
            ∑ x : Fin (k + (l' + 1) + 1), ((-1 : ℂ) ^ (x : ℕ)) * tL x := by
      simpa [tL, tR] using
        (alternatizeUncurryFin_domCoprod_alternatization_wedge_right_core (n := n)
          (k := k) (l := l' + 1) (v := v) (A := A) (B := B))

    have hsum :
        (∑ x : Fin (k + (l' + 1) + 1), (-1) ^ (x : ℕ) * tL x) = (k + 1 : ℂ)⁻¹ * tR := by
      -- Divide by `(k+1)` using the core lemma.
      have hsumNat :
          (k + 1 : ℂ)⁻¹ * tR =
            ∑ x : Fin (k + (l' + 1) + 1), ((-1 : ℂ) ^ (x : ℕ)) * tL x := by
        -- multiply `hreindexNat` by `(k+1)⁻¹` on the left
        have := congrArg (fun z : ℂ => (k + 1 : ℂ)⁻¹ * z) hreindexNat
        -- simplify
        simpa [mul_assoc, hk10, inv_mul_cancel₀ hk10] using this
      -- `hsumNat` is exactly the desired statement, up to symmetry.
      simpa using hsumNat.symm

    -- Multiply `hsum` by `c` to match the rewritten goal.
    simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z : ℂ => c * z) hsum

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
  classical
  -- Expand `alternatizeUncurryFin` and the wedge definition into explicit sums.
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousAlternatingMap.smul_apply]
  simp only [ContinuousAlternatingMap.wedge_apply,
    ContinuousAlternatingMap.wedgeAlternating,
    ContinuousAlternatingMap.wedgeAlternatingTensor,
    ContinuousAlternatingMap.domDomCongr_apply,
    AlternatingMap.domDomCongr_apply,
    LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod'_apply,
    AlternatingMap.domCoprod_apply,
    MultilinearMap.sum_apply]
  -- The remaining step is the signed reindexing that contributes the graded sign (-1)^k.
  -- TODO (Agent 1): implement the explicit reindexing/bijection and sign tracking.
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
