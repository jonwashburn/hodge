# Lean Infrastructure Status

**Date:** 2026-03-17

## Scope

This note records the outcome of the Lean-side infrastructure pass corresponding
to manuscript repair Phases 1--3 of the unconditionality plan.

## A1: `chart_deriv_bound_exists`

- A direct proof attempt was made in
  `Hodge/WorkInProgress/GMT/ManifoldMollifier.lean`.
- On the chart source, the existing theorem
  `mfderivChartAt_norm_pow_le_on_source` gives the desired bound immediately.
- Off the chart source, `mfderivChartAt` appears to simplify to `0` in a simple
  scratch probe, but the full proof still runs into an unresolved branch where
  Lean asks for control of the `MDifferentiableAt` case off source.
- The attempted direct proof was reverted so the build remains stable.

**Status:** not discharged.

## A2: `chart_contMDiff`

- This still appears to be a structural API issue rather than a theorem that is
  cleanly provable as currently stated.
- The current chart-step pipeline in
  `Hodge/WorkInProgress/GMT/CurrentPushforward.lean` and
  `Hodge/WorkInProgress/Analytic/Pullback.lean`
  requires a globally smooth total map `f : X → TangentModel n`.
- For the chart map `chartAt ... x₀`, that is precisely the artificial part.
- The likely honest fix remains a `ContMDiffOn` / source-restricted refactor.

**Status:** not discharged; refactor still needed.

## A3: `euclidean_regularize_isClosed_of_isCycleAt`

- The closest existing ingredients remain:
  - `hasFDerivAt_translateBCF`
  - `shifted_bump_contDiff_joint`
  - `modelTestFormToBCF_shiftedBumpTestForm`
  - `regularizeModelCurrentRaw_eq_extended`
  - `LocalCurrent.boundary_toLinear`
  - `LocalCurrent.isCycleAt_succ_iff`
- The missing bridge is still the derivative-vs-boundary identification needed
  to turn differentiation in the `x` parameter into vanishing of the boundary of
  the model current.

**Status:** not discharged.

## Alignment with repaired manuscripts

- Paper I now exports local face-trace control only in flat norm, not as a
  mass-small current equality.
- Paper II now exports a more explicit `A1`/`A2`/`A3` packet contract with a
  fixed chartwise model-space view of the dictionary.
- Paper III now makes the integral-flat-norm and modulo-torsion class language
  explicit.

These repairs clarify the intended decomposition of `A10`:

1. Paper I = local holomorphic manufacturing
2. Paper II = coherent packet assembly
3. Paper III = exact-class gluing and almost-calibration

The Lean proof spine still compresses all of that into the single axiom-backed
`AutomaticSYRData` interface.

## Conclusion

This cycle did not discharge `A1`--`A3`, but it did sharpen the exact place
where the infrastructure work remains:

- `A1` is closer than before but still blocked by the off-source differentiability branch.
- `A2` still wants a source-restricted chart refactor.
- `A3` still wants the Euclidean derivative/boundary commutation proof.
