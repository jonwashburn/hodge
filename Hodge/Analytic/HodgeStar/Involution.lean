import Hodge.Analytic.HodgeStar.FiberStar

/-!
# Hodge star involution (skeleton)

Classically, on a real `dim`-dimensional oriented inner product space, the Hodge star satisfies

`⋆(⋆α) = (-1)^{k(dim-k)} α`.

Here we record the analogous *fiber-level* involution statement for the model-space fibers
`FiberAlt n k`. Since the real metric-induced construction is not yet implemented, the proof
is left as a TODO (and is currently `sorry`).

This file is **off proof track** unless explicitly imported.
-/

noncomputable section

open Classical

set_option autoImplicit false

/-- Sign factor for the Hodge star involution on a `2n`-dimensional space, as a complex scalar.

This matches the classical exponent `k(2n-k)`. -/
def fiberHodgeStarSign (n k : ℕ) : ℂ :=
  ((-1 : ℤ) ^ (k * (2 * n - k)) : ℂ)

/-- Hodge star is an involution up to sign (fiber-level statement).

**TODO**: Replace `fiberHodgeStar_construct` with the genuine metric construction and prove this
using an orthonormal basis computation. -/
theorem fiberHodgeStar_involution (n k : ℕ) (hk : k ≤ 2 * n) (α : FiberAlt n k) :
    (Nat.sub_sub_self hk ▸
        fiberHodgeStar_construct n (2 * n - k) (fiberHodgeStar_construct n k α)) =
      fiberHodgeStarSign n k • α := by
  sorry
