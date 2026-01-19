import Hodge.Analytic.HodgeStar.FiberStar

/-!
# Smoothness infrastructure for Hodge star (skeleton)

This file is a placeholder for Sprint 2+ work: once a *nontrivial* fiber-level Hodge star is
constructed and promoted to a bundle operator on `SmoothForm`, we will need to prove that it
preserves smoothness (i.e. the coefficient map remains `ContMDiff`).

At the moment, the fiber-level construction in `FiberStar.lean` is a stub, and the proof track
uses the separate `Hodge/Analytic/Norms.lean` `HodgeStarData.trivial` operator.

This module is **off proof track** unless explicitly imported.
-/

noncomputable section

open Classical

set_option autoImplicit false

/-!
## TODO

1. Define the promoted star on sections:
   `SmoothForm n X k → SmoothForm n X (2*n-k)`.
2. Prove `ContMDiff` smoothness of the promoted coefficient map.
3. Prove linearity and `⋆⋆ = ± id` once the metric/volume-form infrastructure exists.
-/
