import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.Abel
import Hodge.Analytic.Currents

/-!
# Prefix template extension (TeX: `prop:sliver-template-extension`)

This file formalizes the purely combinatorial bookkeeping used in the TeX “sliver”/template
machinery:

If two objects are built from **prefixes of a common ordered template** (lengths `N₁`, `N₂`),
then the mismatch decomposes into a **matched** part (indices `< min N₁ N₂`) and an
**unmatched tail** (indices in the longer prefix but not the shorter).

No geometry is used here; this is just `Finset.range` algebra.
-/

noncomputable section

open Classical
open scoped BigOperators

namespace Hodge.TexSpine.Template

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]

/-! ## Prefix sums -/

/-- The current obtained by summing the first `N` template pieces. -/
noncomputable def prefixSum {k : ℕ} (T : ℕ → Current n X k) (N : ℕ) : Current n X k :=
  ∑ i in Finset.range N, T i

@[simp] lemma prefixSum_zero {k : ℕ} (T : ℕ → Current n X k) : prefixSum (n := n) (X := X) T 0 = 0 := by
  simp [prefixSum]

/-- `prefixSum` splits at `Nmin = min N₁ N₂`. -/
theorem prefixSum_split_min {k : ℕ} (T : ℕ → Current n X k) (N₁ N₂ : ℕ) :
    prefixSum (n := n) (X := X) T N₁ =
      prefixSum (n := n) (X := X) T (Nat.min N₁ N₂) +
        ∑ i in (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)), T i := by
  classical
  -- split `range N₁` into the part below `min` and the tail.
  symm
  -- `A = (A ∩ B) ∪ (A \ B)` for `B = range (min ...)`, and the union is disjoint.
  have hdisj :
      Disjoint (Finset.range (Nat.min N₁ N₂))
        (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)) := by
    exact Finset.disjoint_sdiff
  have hsubset : Finset.range (Nat.min N₁ N₂) ⊆ Finset.range N₁ := by
    intro i hi
    -- `i < min N₁ N₂` implies `i < N₁`
    have : i < Nat.min N₁ N₂ := by
      simpa [Finset.mem_range] using hi
    have : i < N₁ := lt_of_lt_of_le this (Nat.min_le_left _ _)
    simpa [Finset.mem_range] using this
  -- now use `sum_subset`/`sum_union` on finsets.
  have hrange : Finset.range N₁ =
      Finset.range (Nat.min N₁ N₂) ∪ (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)) := by
    -- standard `union_sdiff_of_subset`.
    simpa [Finset.union_sdiff_of_subset hsubset]
  -- rewrite and use `Finset.sum_union` with disjointness.
  -- Note: `Finset.sum_union` expects disjointness of the two finsets.
  rw [prefixSum, hrange, Finset.sum_union hdisj]
  -- both sides are now definitional
  simp

/-! ## Unmatched tail decomposition -/

/-- **Matched + unmatched tail decomposition** (TeX: `prop:sliver-template-extension`).

Let `S₁ = prefixSum T N₁` and `S₂ = prefixSum T N₂` be built from the same ordered template.
Then the mismatch decomposes as:

`S₁ - S₂ = (matched) + (unmatched)`

where the matched part uses indices `< min N₁ N₂` on both sides and the unmatched part
is supported on the tail indices of the longer prefix.
-/
theorem prefix_mismatch_decompose {k : ℕ} (T : ℕ → Current n X k) (N₁ N₂ : ℕ) :
    prefixSum (n := n) (X := X) T N₁ - prefixSum (n := n) (X := X) T N₂ =
      (∑ i in (Finset.range N₁ \ Finset.range (Nat.min N₁ N₂)), T i) -
      (∑ i in (Finset.range N₂ \ Finset.range (Nat.min N₁ N₂)), T i) := by
  classical
  -- Expand both prefix sums at `min`, then cancel the common prefix.
  have h1 := prefixSum_split_min (n := n) (X := X) (k := k) T N₁ N₂
  have h2raw := prefixSum_split_min (n := n) (X := X) (k := k) T N₂ N₁
  have h2 :
      prefixSum (n := n) (X := X) T N₂ =
        prefixSum (n := n) (X := X) T (Nat.min N₁ N₂) +
          ∑ i in (Finset.range N₂ \ Finset.range (Nat.min N₁ N₂)), T i := by
    -- rewrite `min N₂ N₁` as `min N₁ N₂`
    simpa [Nat.min_comm] using h2raw
  -- Substitute and let `abel` cancel the shared prefix sum.
  -- `abel` works since `Current n X k` is an additive commutative group.
  -- (Registered in `Hodge/Analytic/Currents.lean`.)
  -- After rewriting, the goal is a purely additive identity.
  simpa [h1, h2, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (by
    -- abel closes the remaining additive goal
    abel)

end Hodge.TexSpine.Template
