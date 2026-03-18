# Unconditionality Audit

**Date:** 2026-03-17  
**Scope:** core manuscripts, standalone package, and Lean proof spine

## Summary

The manuscript package is now substantially more honest about scope and export
contracts than it was at the start of this cycle. Papers I--III and the capstone
have been synchronized so that the series now reads as a coherent conditional
program rather than a monolithic proof sketch. However, the project is still not
an unconditional proof.

The dominant remaining blockers are:

1. unresolved proof-level gaps in the core local geometric assembly (Papers I-II),
2. one still-underjustified bridge in the period/gluing layer (Paper III), and
3. unresolved Lean-side infrastructure and proof-spine axioms, especially `A2`,
   `A3`, `A9`, and `A10`.

## Manuscript-side status

### Paper I
File: `proof_package_standalone_2026-03-17/manuscripts/local_holomorphic_microstructures.tex`

- The local face-trace export has been weakened from a mass-small current-error
  statement to a flat-norm approximation statement.
- The impossible infinite `\delta`-separated parameter-family claim has been
  removed and replaced by a finite-packing statement with repetitions allowed.
- The local multi-sheet theorem has been weakened from “graph over the exact
  footprint” to “graph on a neighborhood containing the footprint”.
- The shared-face theorem has been weakened to flat-norm agreement with a common
  model face current, rather than exact equality plus an explicit error current.

**Status:** more honest, but still not fully unconditional. The finite-anchor
simultaneous interpolation step (`prop:multi-ball`) remains under-justified.

### Paper II
File: `proof_package_standalone_2026-03-17/manuscripts/coherent_assembly_packets_from_cone_forms.tex`

- The direction dictionary is now treated in a fixed chartwise model space,
  removing the most obvious mismatch between the Lipschitz weight lemma and the
  moving dictionary.
- The parameter schedule now explicitly chooses `\eps_h := h\delta(h)` and
  requires `\eps_{\mathrm{hol}} \le \delta(h)`, closing the earlier mismatch in
  the `A1` asymptotics.
- The coherence argument no longer relies on pairwise “may be chosen” reuse of the
  same holomorphic sheet. It now cancels shared model face currents and absorbs
  the Paper I error in flat norm.
- The theorem statement now includes the basepoints `x_Q`, matching Paper III’s
  import contract more closely.

**Status:** improved, but still not fully unconditional. The `O(h)` weight
stability and global coherence estimates are more consistent than before, yet the
 mesh-wide packet existence theorem still depends on a substantial amount of
 quantitative bookkeeping that has not been independently re-audited line by line.

### Paper III
File: `proof_package_standalone_2026-03-17/manuscripts/global_gluing_exact_periods_and_fixed_class_realization.tex`

- The title and prose now consistently say “fixed class modulo torsion”.
- The period-control section now explicitly identifies `\widehat\beta(x_Q)` and
  `\Bary(S_Q)` inside one chartwise model space.
- The gluing proposition now states that `\calF` is the integral flat norm.
- A new lemma makes explicit that matching periods on an integral basis of the
  free part of cohomology determines the homology class modulo torsion.

**Status:** closest of the three to a referee-safe theorem, but the core
`lem:period-control` still compresses nontrivial chartwise computations into
`O(h)` language and would benefit from a fuller coordinate-free argument or an
expanded local proof.

### Capstone and flagship paper

- The capstone now imports Papers I--III by explicit theorem number and matches
  the Paper III contract, including `(A3)` and the modulo-torsion class language.
- The flagship skeleton has been resynced to the repaired interface language.

**Status:** conditional wrapper is now coherent with the repaired core papers.

## Standalone package status

The handoff package at `proof_package_standalone_2026-03-17/` is now free of
internal planning and referee-note files. It contains only the manuscript-facing
materials and compiles for the revised flagship and Papers I--III.

**Status:** handoff-ready as a conditional series package, not as an unconditional proof package.

## Lean-side status

### Infrastructure axioms

- `A1 chart_deriv_bound_exists`: a direct discharge attempt was started, using
  the fact that `mfderivChartAt = id` on the chart source and appears to simplify
  to `0` off source. The attempt was reverted because the “differentiable off
  source” branch still needs a real argument, and the direct proof was not yet
  build-stable.
- `A2 chart_contMDiff`: still a structural API blocker. The current chart-step
  pushforward/pullback layer requires a globally smooth total map; the likely
  honest fix is still a `ContMDiffOn` / source-restricted refactor.
- `A3 euclidean_regularize_isClosed_of_isCycleAt`: still open. Existing lemmas
  (`hasFDerivAt_translateBCF`, `shifted_bump_contDiff_joint`, etc.) appear close
  to the needed theorem, but the key derivative-vs-boundary identification has
  not yet been formalized.

### Proof-spine axioms

- `A9 spine_bridge_cohomology_eq`: still open.
- `A10 microstructure_syr_existence`: still open.

These remain the dominant proof-spine conditionalities in Lean.

## Decision gate

### Current classification

- Paper I face-trace export: `proved after weakening`, but still not fully secure.
- Paper II coherent packet theorem: `not yet secure enough for unconditional use`.
- Paper III exact-class locking modulo torsion: `substantially improved, but still not fully secure`.
- Lean infrastructure `A1-A3`: `not discharged`.
- Lean proof-spine `A9-A10`: `not discharged`.

## Conclusion

The project is closer to an honest conditional series than before this repair
cycle, but it is not yet an unconditional proof. The current highest-value next
work items remain:

1. finish the Paper I finite-anchor / local face-trace repair,
2. fully stabilize Paper II’s global packet theorem,
3. strengthen Paper III’s period-control proof,
4. remove `A2` by a source-restricted chart API refactor,
5. prove `A3`,
6. only then return to `A9` and `A10`.
