# Build Performance Analysis

**Date**: 2026-01-21  
**Task**: R12-A5-PERF

## Build Environment

- **Lean version**: 4.27.0-rc1
- **Mathlib**: leanprover-community/mathlib4 @ 92019987ed6c5b2396fa4042ce2fd72c6125b5b5

## File Size Analysis

Top 20 largest Lean files by line count:

| Lines | File | Notes |
|-------|------|-------|
| 2048 | `Hodge/Analytic/Advanced/LeibnizRule.lean` | Wedge product Leibniz rule |
| 1512 | `Hodge/Analytic/Currents.lean` | Current infrastructure |
| 1231 | `Hodge/Analytic/Advanced/ContMDiffForms.lean` | Smooth form foundations |
| 1218 | `Hodge/Kahler/Microstructure.lean` | SYR construction |
| 990 | `Hodge/Cohomology/Basic.lean` | Cohomology definitions |
| 855 | `Hodge/Analytic/Forms.lean` | SmoothForm structure |
| 745 | `Hodge/Analytic/Norms.lean` | Comass norms |
| 661 | `Hodge/Analytic/FlatNorm.lean` | Flat norm topology |
| 544 | `Hodge/Analytic/DomCoprod.lean` | Domain coproduct |
| 451 | `Hodge/Classical/GAGA.lean` | Serre GAGA |
| 447 | `Hodge/Analytic/Integration/HausdorffMeasure.lean` | Measure integration |
| 442 | `Hodge/Analytic/Grassmannian.lean` | Grassmannian geometry |
| 404 | `Hodge/Analytic/HodgeLaplacian.lean` | Laplacian + harmonics |
| 393 | `Hodge/Classical/HarveyLawson.lean` | Harvey-Lawson theorem |
| 356 | `Hodge/Analytic/IntegralCurrents.lean` | Integral current space |
| 320 | `Hodge/Analytic/Integration/TopFormIntegral.lean` | Top-form integration |
| 315 | `Hodge/Kahler/Main.lean` | Main theorem |
| 313 | `Hodge/GMT/FedererFleming.lean` | Compactness theorem |
| 313 | `Hodge/Analytic/ManifoldForms.lean` | Manifold form utilities |
| 309 | `Hodge/Classical/CycleClass.lean` | Cycle class map |

## Build Timing (from Round 6 baseline)

From `docs/BUILD_PERFORMANCE_BASELINE.md`:

```text
real 25.45
user 23.97
sys  48.51
```

This was measured after `lake exe cache get` (Mathlib pre-compiled).

## Build Job Counts

| Target | Jobs | Notes |
|--------|------|-------|
| `lake build Hodge.Main` | ~3046 | Main proof module only |
| `lake build` (full) | ~6082 | All modules + tests |
| `lake build Hodge.Analytic.IntegralCurrents` | ~2664 | Core analytic module |

## Observations

### Potentially Slow Files

1. **`LeibnizRule.lean` (2048 lines)**: Contains complex shuffle permutation proofs for the Leibniz rule. These proofs involve combinatorial reasoning that may take longer to elaborate.

2. **`Currents.lean` (1512 lines)**: Infrastructure file with many definitions and theorems. Imports are heavy (measure theory, manifolds).

3. **`ContMDiffForms.lean` (1231 lines)**: Foundation for smooth forms on manifolds. Import chain is deep.

4. **`Microstructure.lean` (1218 lines)**: SYR construction with many definitions. Contains complex proof terms.

### Build Parallelization

Lake automatically parallelizes independent module builds. The current structure is well-suited for parallel compilation:

- `Hodge/Analytic/` modules can build in parallel with `Hodge/Classical/`
- `Hodge/GMT/` is mostly independent
- `Hodge/Kahler/` depends on most other modules (later in build order)

### Recommendations

1. **No splitting needed**: The largest files (1000-2000 lines) are within reasonable bounds for Lean. Splitting would add import complexity without significant gains.

2. **Consider caching**: The test files (`Hodge/Tests/`) could be built only when needed, not as part of the main build.

3. **Incremental builds**: After initial build, incremental changes compile in seconds.

## Verification Commands

```bash
# Time full build
/usr/bin/time -p lake build

# Time specific module
/usr/bin/time -p lake build Hodge.Kahler.Microstructure

# Check job counts
lake build Hodge.Main 2>&1 | grep -E "Built|jobs"
```

## Conclusion

Build performance is acceptable (~25-30 seconds for full build with cached Mathlib). No critical performance issues identified. The file structure supports parallel compilation well.
